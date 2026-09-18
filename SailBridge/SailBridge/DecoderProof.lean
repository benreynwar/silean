import SailBridge.DecoderCorrespondence
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Rewrite
import Lean.Elab.Tactic.Simp

/-!
Factored proofs about the actual generated backward decoder.  The small
partial evaluator below does not add an axiom or evaluate native code: it
constructs an ordinary equality proof which Lean's kernel checks.  It exposes
one generated clause at a time and never asks a generic rewrite tactic to
traverse the unreachable tail of Sail's enormous generated mapping.
-/

open Lean Meta Elab Tactic

private theorem generatedBaseEFalse :
    LeanRV32D.Functions.base_E_enabled = false := rfl

/-- Contract one state-monad bind once a separate, small proof has evaluated
its action.  This keeps the proof of a generated tuple decoder from unfolding
the continuation while it evaluates the first component. -/
private theorem bind_apply_of_ok {error state result nextResult : Type}
    (action : EStateM error state result)
    (continuation : result → EStateM error state nextResult)
    (before after : state) (value : result)
    (actionOk : action before = .ok value after) :
    (action >>= continuation) before = continuation value after := by
  simp [bind, EStateM.bind, actionOk]

/-- Perform only beta, zeta, and metadata reduction along the exposed spine.
In particular, this never descends into both arms of a generated decoder
branch. -/
private partial def reduceDecoderSpine : Expr → Expr
  | .letE _ _ value body _ => reduceDecoderSpine (body.instantiate1 value)
  | .app fn argument =>
      match reduceDecoderSpine fn with
      | .lam _ _ body _ => reduceDecoderSpine (body.instantiate1 argument)
      | reducedFn => .app reducedFn argument
  | .mdata _ body => reduceDecoderSpine body
  | expression => expression

private partial def findApplicationOf (name : Name) (expression : Expr) :
    Option Expr :=
  if expression.getAppFn.isConstOf name then some expression
  else
    match expression with
    | .app function argument =>
        findApplicationOf name function <|> findApplicationOf name argument
    | .lam _ type body _ =>
        findApplicationOf name type <|> findApplicationOf name body
    | .forallE _ type body _ =>
        findApplicationOf name type <|> findApplicationOf name body
    | .letE _ type value body _ =>
        findApplicationOf name type <|> findApplicationOf name value <|>
          findApplicationOf name body
    | .mdata _ body => findApplicationOf name body
    | .proj _ _ body => findApplicationOf name body
    | _ => none

private partial def containsNatLiteral (wanted : Nat) : Expr → Bool
  | .lit (.natVal value) => value == wanted
  | .app function argument =>
      containsNatLiteral wanted function || containsNatLiteral wanted argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsNatLiteral wanted type || containsNatLiteral wanted body
  | .letE _ type value body _ =>
      containsNatLiteral wanted type || containsNatLiteral wanted value ||
        containsNatLiteral wanted body
  | .mdata _ body | .proj _ _ body => containsNatLiteral wanted body
  | _ => false

private def proveConstructorDisequality (left right : Expr) :
    TacticM (Option Expr) := do
  let proposition := mkNot (← mkEq left right)
  let proofGoal ← mkFreshExprSyntheticOpaqueMVar proposition
  let savedGoals ← getGoals
  setGoals [proofGoal.mvarId!]
  let succeeded ← observing? (evalTactic (← `(tactic| intro equality; cases equality)))
  let closed := succeeded.isSome && (← getGoals).isEmpty
  setGoals savedGoals
  if closed then return some (← instantiateMVars proofGoal)
  return none

/-- Reduce generated match/projection wrappers until the next actual `if`,
without recursively normalizing either branch. -/
private partial def reduceToDecoderBranch (expression : Expr)
    (fuel : Nat := 100) : MetaM Expr := do
  let expression := reduceDecoderSpine expression
  if expression.isAppOfArity ``ite 6 || fuel = 0 then
    return expression
  if let some reduced ← withTransparency .all (reduceRecMatcher? expression) then
    return ← reduceToDecoderBranch reduced (fuel - 1)
  if let some function ← withTransparency .all
      (reduceProj? expression.getAppFn) then
    return ← reduceToDecoderBranch
      (mkAppN function expression.getAppArgs) (fuel - 1)
  let some unfolded ← unfoldDefinition? expression (ignoreTransparency := true)
    | return expression
  if unfolded == expression then return expression
  reduceToDecoderBranch unfolded (fuel - 1)

/-- Discharge one exposed generated decoder guard.  The simplification set is
limited to the small generated operand predicates and configuration queries;
`bv_decide` then proves the resulting bit-vector proposition. -/
private def proveDecoderGuard (proposition : Expr) : TacticM Expr := do
  if let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedNtlEncoding proposition then
    let arguments := encoding.getAppArgs
    if arguments.size = 1 then
      let proof ← mkAppM ``RV32I.SailBridge.generatedNtl_guard_true
        #[arguments[0]!]
      let proofType ← inferType proof
      if ← withTransparency .all (isDefEq proposition proofType) then
        return mkApp2 (mkConst ``id [0]) proposition proof
  if let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedRtypeEncoding proposition then
    let arguments := encoding.getAppArgs
    if arguments.size = 4 && containsNatLiteral 24595 proposition then
      let proof ← mkAppM
        ``RV32I.SailBridge.generatedRtype_zicbop_guard_false
        #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!]
      let proofType ← inferType proof
      if ← withTransparency .all (isDefEq proposition proofType) then
        return mkApp2 (mkConst ``id [0]) proposition proof
    if arguments.size = 4 && (findApplicationOf
        ``LeanRV32D.Functions.encdec_ntl_backwards_matches proposition).isSome then
      for localDecl in (← getLCtx) do
        let localType ← instantiateMVars localDecl.type
        if ← withTransparency .all (isDefEq proposition localType) then
          return mkFVar localDecl.fvarId
      if let some notAdd ← proveConstructorDisequality arguments[3]!
          (mkConst ``LeanRV32D.rop.ADD) then
        let proof ← mkAppM
          ``RV32I.SailBridge.generatedRtype_ntl_guard_false
          #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!, notAdd]
        let proofType ← inferType proof
        if ← withTransparency .all (isDefEq proposition proofType) then
          return mkApp2 (mkConst ``id [0]) proposition proof
  if let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedZicbopEncoding proposition then
    let arguments := encoding.getAppArgs
    if arguments.size = 3 then
      let proof ← mkAppM ``RV32I.SailBridge.generatedZicbop_guard_true
        #[arguments[0]!, arguments[1]!, arguments[2]!]
      let proofType ← inferType proof
      if ← withTransparency .all (isDefEq proposition proofType) then
        return mkApp2 (mkConst ``id [0]) proposition proof
  let proofGoal ← mkFreshExprSyntheticOpaqueMVar proposition
  let savedGoals ← getGoals
  setGoals [proofGoal.mvarId!]
  evalTactic (← `(tactic|
    first
    | assumption
    | (solve | simp only [
        Bool.not_eq_true,
        RV32I.SailBridge.generatedZicbopEncoding_operation,
        RV32I.SailBridge.generatedZicbopEncoding_rs1,
        RV32I.SailBridge.generatedZicbopEncoding_low15,
        RV32I.SailBridge.generatedZicbopEncoding_operation_core,
        RV32I.SailBridge.generatedZicbopEncoding_rs1_core,
        RV32I.SailBridge.generatedZicbopEncoding_low15_core,
        RV32I.SailBridge.generatedZicbop_guard_true,
        LeanRV32D.Functions.encdec_cbop_zicbop_forwards,
        LeanRV32D.Functions.encdec_cbop_zicbop_backwards_matches,
        RV32I.SailBridge.encdec_reg_backwards_matches_rv32])
    | (simp only [
      Bool.not_eq_true,
      RV32I.SailBridge.generatedUtypeEncoding,
      RV32I.SailBridge.generatedJalEncoding,
      RV32I.SailBridge.generatedJalrEncoding,
      RV32I.SailBridge.generatedBtypeEncoding,
      RV32I.SailBridge.generatedBtypeEncodingWithFunct3,
      RV32I.SailBridge.generatedItypeEncoding,
      RV32I.SailBridge.generatedItypeEncodingWithFunct3,
      RV32I.SailBridge.generatedZicbopEncoding_operation,
      RV32I.SailBridge.generatedZicbopEncoding_rs1,
      RV32I.SailBridge.generatedZicbopEncoding_low15,
      RV32I.SailBridge.generatedShiftEncoding,
      RV32I.SailBridge.generatedShiftUpper,
      RV32I.SailBridge.generatedRtypeFunct3,
      RV32I.SailBridge.generatedRtypeFunct7,
      RV32I.SailBridge.generatedRtypeEncoding_rs2_core,
      RV32I.SailBridge.generatedRtypeEncoding_funct7,
      RV32I.SailBridge.generatedRtypeEncoding_funct7_core,
      RV32I.SailBridge.generatedRtypeEncoding_rs2,
      RV32I.SailBridge.generatedRtypeEncoding_rs1,
      RV32I.SailBridge.generatedRtypeEncoding_funct3,
      RV32I.SailBridge.generatedRtypeEncoding_rd,
      RV32I.SailBridge.generatedRtypeEncoding_opcode,
      RV32I.SailBridge.generatedRtypeEncoding_opcode_core,
      RV32I.SailBridge.generatedRtypeEncoding_opcode_beq_core,
      RV32I.SailBridge.generatedRtype_uop_matcher_false,
      RV32I.SailBridge.generatedRtype_uop_match_false,
      RV32I.SailBridge.generatedRtypeEncoding_low20,
      RV32I.SailBridge.generatedRtypeEncoding_low20_core,
      RV32I.SailBridge.generatedRtypeEncoding_low15,
      RV32I.SailBridge.generatedRtypeEncoding_low15_core,
      RV32I.SailBridge.generatedRtypeEncoding_low12,
      RV32I.SailBridge.generatedRtypeEncoding_low12_core,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_low20,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_low15,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_low12,
      RV32I.SailBridge.generatedRtypeEncoding_ne_pause,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_ne_pause,
      RV32I.SailBridge.NtlInterposes,
      RV32I.SailBridge.generatedNtlEncoding,
      RV32I.SailBridge.generatedItypeEncoding_immediate,
      RV32I.SailBridge.generatedItypeEncoding_rs1,
      RV32I.SailBridge.generatedItypeEncoding_funct3,
      RV32I.SailBridge.generatedItypeEncoding_rd,
      RV32I.SailBridge.generatedItypeEncoding_opcode,
      RV32I.SailBridge.generatedItypeEncodingWithFunct3_immediate,
      RV32I.SailBridge.generatedItypeEncodingWithFunct3_rs1,
      RV32I.SailBridge.generatedItypeEncodingWithFunct3_funct3,
      RV32I.SailBridge.generatedItypeEncodingWithFunct3_rd,
      RV32I.SailBridge.generatedItypeEncodingWithFunct3_opcode,
      RV32I.SailBridge.generatedShiftEncoding_funct6,
      RV32I.SailBridge.generatedShiftEncoding_shamt,
      RV32I.SailBridge.generatedShiftEncoding_rs1,
      RV32I.SailBridge.generatedShiftEncoding_funct3,
      RV32I.SailBridge.generatedShiftEncoding_rd,
      RV32I.SailBridge.generatedShiftEncoding_opcode,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_funct7,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_funct7_core,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_rs2,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_rs2_core,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_rs1,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_funct3,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_rd,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_opcode,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_opcode_core,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_low20_core,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_low15_core,
      RV32I.SailBridge.generatedRtypeEncodingWithFields_low12_core,
      RV32I.SailBridge.generatedNtlEncoding_eq,
      RV32I.SailBridge.generatedNtl_guard_true,
      LeanRV32D.Functions.encdec_reg_forwards,
      RV32I.SailBridge.sailRegister,
      LeanRV32D.Functions.encdec_uop_forwards,
      LeanRV32D.zero_extend, Sail.BitVec.zeroExtend,
      Sail.BitVec.extractLsb,
      LeanRV32D.Functions.encdec_cbop_zicbop_backwards_matches,
      LeanRV32D.Functions.encdec_cbop_zicbop_forwards,
      RV32I.SailBridge.encdec_reg_backwards_matches_rv32,
      RV32I.SailBridge.encdec_reg_forwards_zero,
      LeanRV32D.Functions.encdec_ntl_forwards,
      LeanRV32D.Functions.encdec_bop_backwards_matches,
      LeanRV32D.Functions.encdec_bop_forwards,
      LeanRV32D.Functions.encdec_iop_backwards_matches,
      LeanRV32D.Functions.encdec_iop_forwards,
      LeanRV32D.Functions.encdec_sop_forwards,
      LeanRV32D.Functions.encdec_uop_backwards_matches,
      LeanRV32D.Functions.xlen,
      LeanRV32D.Functions.currentlyEnabled,
      LeanRV32D.Functions.hartSupports,
      generatedBaseEFalse,
      LeanRV32D.Functions.not, Sail.BitVec.access,
      pure, EStateM.pure] <;>
    (try dsimp only [LeanRV32D.Functions.base_E_enabled]) <;>
    bv_decide)))
  unless (← getGoals).isEmpty do
    throwError "generated decoder guard proof left goals"
  setGoals savedGoals
  instantiateMVars proofGoal

private def liftNegationToCondition (condition rawProof : Expr) : MetaM Expr :=
  withLocalDeclD `generatedDecoderGuard condition fun guard => do
    let rawType ← withTransparency .all (whnf (← inferType rawProof))
    let .forallE _ rawCondition _ _ := rawType
      | throwError "generated raw guard proof is not a negation"
    let liftedGuard := mkApp2 (mkConst ``id [0]) rawCondition guard
    let contradiction := mkApp rawProof liftedGuard
    discard <| inferType contradiction
    mkLambdaFVars #[guard] contradiction

private def chooseDecoderBranch (condition : Expr)
    (decoderFuel? : Option Nat := none) : TacticM (Bool × Expr) := do
  if let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedRtypeEncoding condition then
    let arguments := encoding.getAppArgs
    if arguments.size = 4 && (findApplicationOf
        ``LeanRV32D.Functions.encdec_uop_backwards_matches condition).isSome then
      let rawProof ← mkAppM
        ``RV32I.SailBridge.generatedRtype_utype_clause_guard_false
        #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!]
      let proof ← liftNegationToCondition condition rawProof
      return (false, proof)
    if arguments.size = 4 && containsNatLiteral 16777231 condition then
      let rawProof ← mkAppM
        ``RV32I.SailBridge.generatedRtype_pause_guard_false
        #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!]
      let proof ← liftNegationToCondition condition rawProof
      return (false, proof)
    if arguments.size = 4 && (findApplicationOf
        ``LeanRV32D.Functions.encdec_ntl_backwards_matches condition).isSome then
      let mut rawProof? : Option Expr := none
      for localDecl in (← getLCtx) do
        if localDecl.userName == `notNtl || localDecl.userName == `ntlGuard ||
            (findApplicationOf
              ``LeanRV32D.Functions.encdec_ntl_backwards_matches
              localDecl.type).isSome then
          rawProof? := some (mkFVar localDecl.fvarId)
      if rawProof?.isNone then
        if let some notAdd ← proveConstructorDisequality arguments[3]!
            (mkConst ``LeanRV32D.rop.ADD) then
          rawProof? := some (← mkAppM
            ``RV32I.SailBridge.generatedRtype_ntl_guard_false
            #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!, notAdd])
      if let some rawProof := rawProof? then
        let proof ← liftNegationToCondition condition rawProof
        return (false, proof)
  if let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedRtypeEncoding condition then
    let arguments := encoding.getAppArgs
    let clauseOperation? := decoderFuel?.bind fun fuel =>
      match fuel with
      | 178 => some (mkConst ``LeanRV32D.rop.ADD)
      | 176 => some (mkConst ``LeanRV32D.rop.SLT)
      | 174 => some (mkConst ``LeanRV32D.rop.SLTU)
      | 172 => some (mkConst ``LeanRV32D.rop.AND)
      | 170 => some (mkConst ``LeanRV32D.rop.OR)
      | 168 => some (mkConst ``LeanRV32D.rop.XOR)
      | 166 => some (mkConst ``LeanRV32D.rop.SLL)
      | 164 => some (mkConst ``LeanRV32D.rop.SRL)
      | 162 => some (mkConst ``LeanRV32D.rop.SUB)
      | 160 => some (mkConst ``LeanRV32D.rop.SRA)
      | _ => none
    if arguments.size = 4 && containsNatLiteral 51 condition &&
        (findApplicationOf
          ``LeanRV32D.Functions.encdec_ntl_backwards_matches condition).isNone then
      if let some clauseOperation := clauseOperation? then
        if ← withTransparency .all
            (isDefEq arguments[3]! clauseOperation) then
          let equalityType ← mkEq arguments[3]! clauseOperation
          let equalityProof := mkApp2 (mkConst ``id [0]) equalityType
            (← mkAppM ``Eq.refl #[clauseOperation])
          let rawProof ← mkAppM
            ``RV32I.SailBridge.generatedRtype_clause_guard_true
            #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!,
              clauseOperation, equalityProof]
          let proof := mkApp2 (mkConst ``id [0]) condition rawProof
          discard <| inferType proof
          return (true, proof)
        else if let some different ←
            proveConstructorDisequality arguments[3]! clauseOperation then
          let rawProof ← mkAppM
            ``RV32I.SailBridge.generatedRtype_clause_guard_false
            #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!,
              clauseOperation, different]
          let proof ← liftNegationToCondition condition rawProof
          return (false, proof)
      else
        throwError m!"unmapped base RTYPE decoder clause fuel {decoderFuel?}"
  if let some proof ← observing? (proveDecoderGuard (mkNot condition)) then
    return (false, proof)
  return (true, ← proveDecoderGuard condition)

/-- Simplify only already-selected operand decoders and monadic plumbing. -/
private def simplifySelectedDecoderClause (expression : Expr) : TacticM Simp.Result := do
  let simpSyntax ← `(tactic| simp only [
    RV32I.SailBridge.generatedUtypeEncoding_immediate,
    RV32I.SailBridge.generatedUtypeEncoding_rd,
    RV32I.SailBridge.generatedUtypeEncoding_opcode,
    RV32I.SailBridge.generatedJalEncoding_bit31,
    RV32I.SailBridge.generatedJalEncoding_bits30_21,
    RV32I.SailBridge.generatedJalEncoding_bit20,
    RV32I.SailBridge.generatedJalEncoding_bits19_12,
    RV32I.SailBridge.generatedJalEncoding_rd,
    RV32I.SailBridge.generatedJalEncoding_opcode,
    RV32I.SailBridge.generatedJalImmediate_roundtrip,
    RV32I.SailBridge.generatedJalrEncoding_immediate,
    RV32I.SailBridge.generatedJalrEncoding_rs1,
    RV32I.SailBridge.generatedJalrEncoding_funct3,
    RV32I.SailBridge.generatedJalrEncoding_rd,
    RV32I.SailBridge.generatedJalrEncoding_opcode,
    RV32I.SailBridge.generatedBtypeEncoding_bit31,
    RV32I.SailBridge.generatedBtypeEncoding_bits30_25,
    RV32I.SailBridge.generatedBtypeEncoding_rs2,
    RV32I.SailBridge.generatedBtypeEncoding_rs1,
    RV32I.SailBridge.generatedBtypeEncoding_funct3,
    RV32I.SailBridge.generatedBtypeEncoding_bits11_8,
    RV32I.SailBridge.generatedBtypeEncoding_bit7,
    RV32I.SailBridge.generatedBtypeEncoding_opcode,
    RV32I.SailBridge.generatedBtypeImmediate_roundtrip,
    RV32I.SailBridge.generatedItypeEncodingWithFunct3_immediate,
    RV32I.SailBridge.generatedItypeEncodingWithFunct3_rs1,
    RV32I.SailBridge.generatedItypeEncodingWithFunct3_funct3,
    RV32I.SailBridge.generatedItypeEncodingWithFunct3_rd,
    RV32I.SailBridge.generatedItypeEncodingWithFunct3_opcode,
    RV32I.SailBridge.generatedShiftEncoding_funct6,
    RV32I.SailBridge.generatedShiftEncoding_shamt,
    RV32I.SailBridge.generatedShiftEncoding_rs1,
    RV32I.SailBridge.generatedShiftEncoding_funct3,
    RV32I.SailBridge.generatedShiftEncoding_rd,
    RV32I.SailBridge.generatedShiftEncoding_opcode,
    RV32I.SailBridge.generatedRtypeEncodingWithFields_funct7,
    RV32I.SailBridge.generatedRtypeEncodingWithFields_rs2,
    RV32I.SailBridge.generatedRtypeEncodingWithFields_rs1,
    RV32I.SailBridge.generatedRtypeEncodingWithFields_funct3,
    RV32I.SailBridge.generatedRtypeEncodingWithFields_rd,
    RV32I.SailBridge.generatedRtypeEncodingWithFields_opcode,
    RV32I.SailBridge.generatedNtlEncoding_eq,
    RV32I.SailBridge.encdec_uop_roundtrip,
    RV32I.SailBridge.encdec_bop_roundtrip,
    RV32I.SailBridge.encdec_iop_roundtrip,
    RV32I.SailBridge.encdec_slli_roundtrip,
    RV32I.SailBridge.encdec_srli_roundtrip,
    RV32I.SailBridge.encdec_reg_roundtrip,
    RV32I.SailBridge.encdec_reg_payload_roundtrip,
    bind, EStateM.bind, pure, EStateM.pure])
  let context ← mkSimpContext simpSyntax.raw (eraseLocal := false)
  return (← Meta.simp expression context.ctx context.simprocs).1

private def transProof (first second : Expr) : MetaM Expr := do
  let firstType ← inferType first
  let secondType ← inferType second
  let some (type, left, middle) := firstType.eq?
    | throwError "first decoder proof is not an equality"
  let some (_, _, right) := secondType.eq?
    | throwError "second decoder proof is not an equality"
  let resultLevel ← getLevel type
  let expectedSecondType ← mkEq middle right
  let liftedSecond :=
    mkApp2 (mkConst ``id [0]) expectedSecondType second
  return mkApp6 (mkConst ``Eq.trans [resultLevel]) type left middle right
    first liftedSecond

/-- Lift an equality for one argument of an application without asking the
generic rewrite engine to search the application's other (potentially huge)
arguments. -/
private def replaceApplicationArgument (expression : Expr)
    (arguments : Array Expr) (index : Nat) (replacement argumentProof : Expr) :
    MetaM (Expr × Expr) := do
  let some original := arguments[index]?
    | throwError "generated decoder application argument index is out of range"
  let originalType ← inferType original
  let newExpression := mkAppN expression.getAppFn
    (arguments.set! index replacement)
  let congruenceProof ← withLocalDeclD `selectedDecoderArgument originalType
    fun selected => do
      let body := mkAppN expression.getAppFn (arguments.set! index selected)
      let function ← mkLambdaFVars #[selected] body
      mkCongrArg function argumentProof
  return (newExpression, congruenceProof)

/-- Expose one state-action constructor, bind matcher, or dependent `if`
without deciding the dependent condition or entering a continuation. -/
private partial def exposeStateAction (expression : Expr)
    (fuel : Nat := 100) : MetaM Expr := do
  let expression := reduceDecoderSpine expression
  if expression.isAppOfArity ``EStateM.bind.match_1 7 ||
      expression.isAppOfArity ``Decidable.rec 6 ||
      expression.isAppOfArity ``EStateM.Result.ok 5 ||
      expression.isAppOfArity ``EStateM.Result.error 4 || fuel = 0 then
    return expression
  if let some reduced ← withTransparency .all (reduceRecMatcher? expression) then
    return ← exposeStateAction reduced (fuel - 1)
  if let some function ← withTransparency .all
      (reduceProj? expression.getAppFn) then
    return ← exposeStateAction
      (mkAppN function expression.getAppArgs) (fuel - 1)
  let some unfolded ← unfoldDefinition? expression (ignoreTransparency := true)
    | return expression
  if unfolded == expression then return expression
  exposeStateAction unfolded (fuel - 1)

/-- Regard a proof whose left endpoint is definitionally reduced as a proof
starting at the unreduced expression. -/
private def liftDefinitionalLeft (original proof : Expr) : MetaM Expr := do
  let proofType ← inferType proof
  let some (_, _, right) := proofType.eq?
    | throwError "state-action step did not produce an equality"
  let desiredType ← mkEq original right
  return mkApp2 (mkConst ``id [0]) desiredType proof

private def specializedZicbopOperandResult? (action state : Expr) :
    TacticM (Option Simp.Result) := do
  let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedZicbopEncoding action
    | return none
  let arguments := encoding.getAppArgs
  if arguments.size != 3 then return none
  let proof ← mkAppM
    ``RV32I.SailBridge.generatedZicbopOperandDecode_encoding
    #[arguments[0]!, arguments[1]!, arguments[2]!, state]
  let proofType ← inferType proof
  let some (_, left, result) := proofType.eq? | return none
  unless ← withTransparency .all (isDefEq action left) do return none
  let liftedProof ← liftDefinitionalLeft action proof
  return some { expr := result, proof? := some liftedProof }

private def specializedItypeOperandResult? (action state : Expr) :
    TacticM (Option Simp.Result) := do
  let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedItypeEncoding action
    | return none
  let arguments := encoding.getAppArgs
  if arguments.size != 4 then return none
  let proof ← mkAppM
    ``RV32I.SailBridge.generatedItypeOperandDecode_encoding
    #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!, state]
  let proofType ← inferType proof
  let some (_, left, result) := proofType.eq? | return none
  unless ← withTransparency .all (isDefEq action left) do return none
  let liftedProof ← liftDefinitionalLeft action proof
  return some { expr := result, proof? := some liftedProof }

private def specializedShiftOperandResult? (action state : Expr) :
    TacticM (Option Simp.Result) := do
  let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedShiftEncoding action
    | return none
  let arguments := encoding.getAppArgs
  if arguments.size != 4 then return none
  let proof ← mkAppM
    ``RV32I.SailBridge.generatedShiftOperandDecode_encoding
    #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!, state]
  let proofType ← inferType proof
  let some (_, left, result) := proofType.eq? | return none
  unless ← withTransparency .all (isDefEq action left) do return none
  let liftedProof ← liftDefinitionalLeft action proof
  return some { expr := result, proof? := some liftedProof }

private def specializedRtypeOperandResult? (action state : Expr) :
    TacticM (Option Simp.Result) := do
  let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedRtypeEncoding action
    | return none
  let arguments := encoding.getAppArgs
  if arguments.size != 4 then return none
  let proof ← mkAppM
    ``RV32I.SailBridge.generatedRtypeOperandDecode_encoding
    #[arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!, state]
  let proofType ← inferType proof
  let some (_, left, result) := proofType.eq? | return none
  unless ← withTransparency .all (isDefEq action left) do return none
  let liftedProof ← liftDefinitionalLeft action proof
  return some { expr := result, proof? := some liftedProof }

private def specializedNtlOperandResult? (action state : Expr) :
    TacticM (Option Simp.Result) := do
  let some encoding := findApplicationOf
      ``RV32I.SailBridge.generatedNtlEncoding action
    | return none
  let arguments := encoding.getAppArgs
  if arguments.size != 1 then return none
  let proof ← mkAppM
    ``RV32I.SailBridge.generatedNtlOperandDecode_encoding
    #[arguments[0]!, state]
  let proofType ← inferType proof
  let some (_, left, result) := proofType.eq? | return none
  unless ← withTransparency .all (isDefEq action left) do return none
  let liftedProof ← liftDefinitionalLeft action proof
  return some { expr := result, proof? := some liftedProof }

/-- Apply an equality at the root of a definitionally equal expression.  No
subexpression search is performed. -/
private def applyEqualityAtRoot (expression proof : Expr) : MetaM (Expr × Expr) := do
  let proofType ← inferType proof
  let some (_, left, right) := proofType.eq?
    | throwError "root replacement proof is not an equality"
  unless expression == left do
    unless ← withTransparency .all (isDefEq expression left) do
      throwError "root replacement proof does not match the expression"
  return (right, ← liftDefinitionalLeft expression proof)

/-- Take exactly one proof-producing step inside a generated state action.
Nested binds are traversed structurally with congruence; their continuations
are never searched or simplified. -/
private partial def advanceStateAction (profileProof : Expr)
    (action : Expr) (fuel : Nat := 100) : TacticM (Option (Expr × Expr)) := do
  if fuel = 0 then
    throwError "generated state-action factoring exhausted its fuel"
  let spine := reduceDecoderSpine action
  if spine.getAppFn.isConstOf ``LeanRV32D.Functions.currentlyEnabled then
    let (replacement, rootProof) ← applyEqualityAtRoot spine profileProof
    let proof ← liftDefinitionalLeft action rootProof
    return some (replacement, proof)

  let exposed ← exposeStateAction action
  if exposed.isAppOfArity ``Decidable.rec 6 then
    let arguments := exposed.getAppArgs
    let (takeTrue, conditionProof) ← chooseDecoderBranch arguments[0]!
    let selectedDecidable ←
      if takeTrue then mkAppM ``Decidable.isTrue #[conditionProof]
      else mkAppM ``Decidable.isFalse #[conditionProof]
    let decidableEq ← mkAppM ``Subsingleton.elim
      #[arguments[4]!, selectedDecidable]
    let (replacement, congruenceProof) ← replaceApplicationArgument exposed
      arguments 4 selectedDecidable decidableEq
    let reduced ←
      match ← withTransparency .all (reduceRecMatcher? replacement) with
      | some result => pure result
      | none => throwError "selected structural state condition did not reduce"
    let reductionType ← mkEq replacement reduced
    let reductionProof := mkApp2 (mkConst ``id [0]) reductionType
      (← mkAppM ``Eq.refl #[reduced])
    let proof ← liftDefinitionalLeft action
      (← transProof congruenceProof reductionProof)
    return some (reduced, proof)

  if exposed.isAppOfArity ``EStateM.bind.match_1 7 then
    let arguments := exposed.getAppArgs
    let nestedOriginal := arguments[4]!
    let nested ← exposeStateAction nestedOriginal
    if nested.isAppOfArity ``EStateM.Result.ok 5 then
      let nestedArguments := nested.getAppArgs
      let selected := mkApp2 arguments[5]! nestedArguments[3]!
        nestedArguments[4]!
      let desiredType ← mkEq action selected
      let proof := mkApp2 (mkConst ``id [0]) desiredType
        (← mkAppM ``Eq.refl #[selected])
      return some (selected, proof)
    if nested.isAppOfArity ``EStateM.Result.error 4 then
      let nestedArguments := nested.getAppArgs
      let selected := mkApp2 arguments[6]! nestedArguments[2]!
        nestedArguments[3]!
      let desiredType ← mkEq action selected
      let proof := mkApp2 (mkConst ``id [0]) desiredType
        (← mkAppM ``Eq.refl #[selected])
      return some (selected, proof)
    let some (nestedNew, nestedProof) ←
        advanceStateAction profileProof nestedOriginal (fuel - 1)
      | return none
    let (newExposed, congruenceProof) ← replaceApplicationArgument exposed
      arguments 4 nestedNew nestedProof
    let proof ← liftDefinitionalLeft action congruenceProof
    return some (newExposed, proof)

  return none

/-- Take a small, explicitly bounded number of structural state-action steps,
composing their kernel-checked equality proofs. -/
private partial def advanceStateActions (profileProof : Expr)
    (action : Expr) : Nat → TacticM (Expr × Expr)
  | 0 => return (action, ← mkAppM ``Eq.refl #[action])
  | steps + 1 => do
      let some (next, firstProof) ← advanceStateAction profileProof action
        | return (action, ← mkAppM ``Eq.refl #[action])
      let (result, tailProof) ←
        advanceStateActions profileProof next steps
      return (result, ← transProof firstProof tailProof)

/-- Construct a proof by following only the selected path through the
generated decoder.  Every structural expectation is checked, so regeneration
which changes the mapping shape causes a bridge build failure rather than a
silently different proof. -/
private partial def proveGeneratedDecode (goal : MVarId) (profileProof : Expr)
    (expression expected : Expr) (reduceFirst : Bool := true)
    (fuel : Nat := 200) : TacticM Expr := do
  if fuel = 0 then
    throwError "generated decoder partial evaluation exhausted its clause fuel"
  /- Generated `do` notation can leave `(bind (pure value) continuation) state`
  at the root after a rejected decoder clause.  Contract that single redex
  directly.  This avoids asking weak-head reduction to traverse the deeply
  nested continuation merely to expose the next clause. -/
  if reduceFirst && expression.getAppFn.isConstOf ``bind then
    let arguments := expression.getAppArgs
    if arguments.size = 7 && arguments[4]!.getAppFn.isConstOf ``pure then
      let pureArguments := arguments[4]!.getAppArgs
      let some value := pureArguments.back?
        | throwError "generated decoder root pure action has no value"
      let selected := mkApp2 arguments[5]! value arguments[6]!
      let desiredType ← mkEq expression selected
      let reductionProof := mkApp2 (mkConst ``id [0]) desiredType
        (← mkAppM ``Eq.refl #[selected])
      let tail ← proveGeneratedDecode goal profileProof selected expected
        true (fuel - 1)
      return ← transProof reductionProof tail
    if arguments.size = 7 &&
        (reduceDecoderSpine arguments[4]!).getAppFn.isConstOf ``bind then
      let appliedAction := mkApp arguments[4]! arguments[6]!
      let simplifiedAction ←
        if let some result ← specializedNtlOperandResult?
            appliedAction arguments[6]! then
          pure result
        else if let some result ← specializedZicbopOperandResult?
            appliedAction arguments[6]! then
          pure result
        else if let some result ← specializedRtypeOperandResult?
            appliedAction arguments[6]! then
          pure result
        else if fuel = 183 then
          let some result ← specializedItypeOperandResult?
              appliedAction arguments[6]!
            | throwError "generated ITYPE clause changed shape"
          pure result
        else if fuel = 181 || fuel = 179 || fuel = 177 then
          let some result ← specializedShiftOperandResult?
              appliedAction arguments[6]!
            | throwError "generated SHIFTIOP clause changed shape"
          pure result
        else
          simplifySelectedDecoderClause appliedAction
      let exposedAction := simplifiedAction.expr
      if exposedAction.isAppOfArity ``EStateM.Result.ok 5 then
        let some actionProof := simplifiedAction.proof?
          | throwError "generated tuple simplification changed a term without a proof"
        let actionArguments := exposedAction.getAppArgs
        let selected := mkApp2 arguments[5]! actionArguments[3]!
          actionArguments[4]!
        let rootProof := mkAppN
          (mkConst ``bind_apply_of_ok)
          #[actionArguments[0]!, actionArguments[1]!, actionArguments[2]!,
            arguments[3]!, arguments[4]!, arguments[5]!, arguments[6]!,
            actionArguments[4]!, actionArguments[3]!, actionProof]
        let rootProof ← liftDefinitionalLeft expression rootProof
        let tail ← proveGeneratedDecode goal profileProof selected expected
          true (fuel - 1)
        return ← transProof rootProof tail
  let expression ←
    if !reduceFirst then pure expression
    else if expression.getAppFn.isConstOf ``bind then
      /- A rejected clause leaves the selected tail as a root-level generic
      `bind`.  Expose only its state-action matcher; asking the ordinary
      decoder reducer to unfold the whole continuation crosses Lean's default
      recursion limit at the BTYPE boundary. -/
      exposeStateAction expression
    else reduceToDecoderBranch expression
  /- Do not ask definitional equality about an exposed `if`: doing so would
  normalize its enormous unselected decoder tail. -/
  if expression.isAppOfArity ``EStateM.Result.ok 5 then
    if expression == expected then
      return ← mkAppM ``Eq.refl #[expected]
  if expression.isAppOfArity ``ite 6 then
    let arguments := expression.getAppArgs
    let (takeTrue, conditionProof) ← chooseDecoderBranch arguments[1]! (some fuel)
    let resultLevel ← getLevel arguments[0]!
    let branchProof :=
      if takeTrue then
        mkApp6 (mkConst ``if_pos [resultLevel]) arguments[1]! arguments[2]!
          conditionProof arguments[0]! arguments[3]! arguments[4]!
      else
        mkApp6 (mkConst ``if_neg [resultLevel]) arguments[1]! arguments[2]!
          conditionProof arguments[0]! arguments[3]! arguments[4]!
    /- `expression` was just checked to be this exposed `ite`, so rewrite
    succeeds at the root and never visits either branch body. -/
    let selected ← goal.rewrite expression branchProof
    unless selected.mvarIds.isEmpty do
      throwError "selecting an exposed generated decoder branch produced side goals"
    let tail ← proveGeneratedDecode goal profileProof selected.eNew expected
      true (fuel - 1)
    return ← transProof selected.eqProof tail

  /- Use ordinary weak-head reduction for the selected clause. -/
  if expression.isAppOfArity ``EStateM.bind.match_1 7 then
    let arguments := expression.getAppArgs
    let innerOriginal := arguments[4]!
    let inner ←
      if reduceFirst then withTransparency .all (whnf innerOriginal)
      else exposeStateAction innerOriginal
    if inner.getAppFn.isConstOf ``LeanRV32D.Functions.currentlyEnabled then
      let (replacement, rootProof) ← applyEqualityAtRoot inner profileProof
      let liftedInnerProof ← liftDefinitionalLeft innerOriginal rootProof
      let (rewrittenOuter, outerProof) ← replaceApplicationArgument expression
        arguments 4 replacement liftedInnerProof
      let (nextExpression, profileStepProof) ←
        advanceStateActions profileProof rewrittenOuter 3
      let tail ← proveGeneratedDecode goal profileProof nextExpression expected
        false (fuel - 1)
      return ← transProof outerProof (← transProof profileStepProof tail)
    if inner.isAppOfArity ``Decidable.rec 6 then
      let innerArguments := inner.getAppArgs
      let (takeTrue, conditionProof) ← chooseDecoderBranch innerArguments[0]!
      let selectedDecidable ←
        if takeTrue then mkAppM ``Decidable.isTrue #[conditionProof]
        else mkAppM ``Decidable.isFalse #[conditionProof]
      let decidableEq ← mkAppM ``Subsingleton.elim
        #[innerArguments[4]!, selectedDecidable]
      let (rewrittenInner, innerCongruenceProof) ←
        replaceApplicationArgument inner innerArguments 4 selectedDecidable decidableEq
      let liftedInnerProof ←
        liftDefinitionalLeft innerOriginal innerCongruenceProof
      let reducedInner ←
        match ← withTransparency .all
            (reduceRecMatcher? rewrittenInner) with
        | some reduced => pure reduced
        | none => throwError "selected dependent decoder condition did not reduce"
      let reductionType ← mkEq rewrittenInner reducedInner
      let reductionProof := mkApp2 (mkConst ``id [0]) reductionType
        (← mkAppM ``Eq.refl #[reducedInner])
      let completeInnerProof ← transProof liftedInnerProof reductionProof
      let (rewrittenOuter, outerProof) ← replaceApplicationArgument expression
        arguments 4 reducedInner completeInnerProof
      let tail ← proveGeneratedDecode goal profileProof rewrittenOuter expected
        reduceFirst (fuel - 1)
      return ← transProof outerProof tail
    if !inner.isAppOfArity ``EStateM.Result.ok 5 then
      if let some (advancedInner, innerProof) ←
          advanceStateAction profileProof innerOriginal then
        let (rewrittenOuter, outerProof) ← replaceApplicationArgument expression
          arguments 4 advancedInner innerProof
        let tail ← proveGeneratedDecode goal profileProof rewrittenOuter expected
          false (fuel - 1)
        return ← transProof outerProof tail
    if inner.isAppOfArity ``EStateM.Result.ok 5 &&
        inner.getAppArgs[3]!.getAppFn.isConstOf ``Option.none then
      if let some (advanced, stepProof) ←
          advanceStateAction profileProof expression then
        let tail ← proveGeneratedDecode goal profileProof advanced expected
          true (fuel - 1)
        return ← transProof stepProof tail

  /- Only simplify after the branch and state-query cases above have removed
  their unreachable continuations. -/
  let simplified ← simplifySelectedDecoderClause expression
  if simplified.expr != expression then
    let some simplificationProof := simplified.proof?
      | throwError "decoder simplification changed a term without a proof"
    let tail ← proveGeneratedDecode goal profileProof simplified.expr expected
      true (fuel - 1)
    return ← transProof simplificationProof tail

  if expression.isAppOfArity ``EStateM.Result.ok 5 then
    if ← withTransparency .all (isDefEq expression expected) then
      return ← mkAppM ``Eq.refl #[expected]

  throwError m!"generated decoder partial evaluation stopped at\n{expression}"

/-- Close an equation for the actual generated backward decoder by following
only its selected clause path.  The supplied equation is the audited decoder
profile fact used for Zicfilp interposition; `rfl` suffices in cases reached
before that query. -/
elab "close_generated_decode " h:term : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, lhs, rhs) := target.eq?
    | throwError "close_generated_decode expects an equality"
  let some unfolded ← unfoldDefinition? lhs (ignoreTransparency := true)
    | throwError "the equation's left side did not expose a definition"
  let profileProof ← elabTerm h none
  let proof ← proveGeneratedDecode goal profileProof unfolded rhs
  goal.assign proof

/-- Concrete regression cases can be reduced definitionally up to the one
state-dependent Zicfilp query.  Keeping this separate avoids manufacturing a
long chain of branch equalities for closed 32-bit constants. -/
elab "close_concrete_generated_decode " h:term : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, lhs, rhs) := target.eq?
    | throwError "close_concrete_generated_decode expects an equality"
  let lhsWhnf ← withTransparency .all (whnf lhs)
  if ← withTransparency .all (isDefEq lhsWhnf rhs) then
    goal.assign (← mkAppM ``Eq.refl #[rhs])
    return
  unless lhsWhnf.isAppOfArity ``EStateM.bind.match_1 7 do
    throwError "concrete generated decode did not stop at the audited state query"
  let innerOriginal := lhsWhnf.getAppArgs[4]!
  let inner ← withTransparency .all (whnf innerOriginal)
  let profileProof ← elabTerm h none
  let rewrittenInner ← goal.rewrite inner profileProof
  unless rewrittenInner.mvarIds.isEmpty do
    throwError "concrete profile rewrite generated side goals"
  let innerEqType ← mkEq innerOriginal rewrittenInner.eNew
  let liftedInnerProof :=
    mkApp2 (mkConst ``id [0]) innerEqType rewrittenInner.eqProof
  let rewrittenOuter ← goal.rewrite lhsWhnf liftedInnerProof
  unless rewrittenOuter.mvarIds.isEmpty do
    throwError "concrete decoder-context rewrite generated side goals"
  unless ← withTransparency .all (isDefEq rewrittenOuter.eNew rhs) do
    throwError "concrete generated result differs from the expected result"
  let tail ← mkAppM ``Eq.refl #[rhs]
  goal.assign (← transProof rewrittenOuter.eqProof tail)

namespace RV32I.SailBridge

open LeanRV32D.Functions

abbrev GeneratedDecodeResult :=
  EStateM.Result (Sail.Error LeanRV32D.exception) SailState
    LeanRV32D.instruction

/-! ## Symbolic base instruction families -/

/-- The actual generated decoder accepts every LUI field combination. -/
theorem generated_decodes_lui (immediate : BitVec 20)
    (rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedUtypeEncoding immediate rd .LUI) sail =
      (.ok (.UTYPE (immediate, sailRegister rd, .LUI)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

/-- The actual generated decoder accepts every AUIPC field combination. -/
theorem generated_decodes_auipc (immediate : BitVec 20)
    (rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedUtypeEncoding immediate rd .AUIPC) sail =
      (.ok (.UTYPE (immediate, sailRegister rd, .AUIPC)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

/-- The complete U-type family, factored through its two generated opcode
constructors. -/
theorem generated_decodes_utype (immediate : BitVec 20)
    (rd : RV32I.Register) (operation : LeanRV32D.uop)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedUtypeEncoding immediate rd operation) sail =
      (.ok (.UTYPE (immediate, sailRegister rd, operation)) sail :
        GeneratedDecodeResult) := by
  cases operation
  · exact generated_decodes_lui immediate rd sail profile
  · exact generated_decodes_auipc immediate rd sail profile

theorem utype_decoders_correspond (immediate : BitVec 20)
    (rd : RV32I.Register) (operation : LeanRV32D.uop) :
    DecodersCorrespondAt (generatedUtypeEncoding immediate rd operation)
      (.UTYPE (immediate, sailRegister rd, operation)) := by
  cases operation
  · change generatedBaseView
      (.UTYPE (immediate, sailRegister rd, .LUI)) =
        RV32I.Decoder.decode (generatedUtypeEncoding immediate rd .LUI)
    rw [generated_lui_encoding_eq_clean, clean_decodes_encoded_lui]
    simp [generatedBaseView]
  · change generatedBaseView
      (.UTYPE (immediate, sailRegister rd, .AUIPC)) =
        RV32I.Decoder.decode (generatedUtypeEncoding immediate rd .AUIPC)
    rw [generated_auipc_encoding_eq_clean, clean_decodes_encoded_auipc]
    simp [generatedBaseView]

/-- The actual generated decoder accepts every JAL field combination. -/
theorem generated_decodes_jal (storedImmediate : BitVec 20)
    (rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedJalEncoding storedImmediate rd) sail =
      (.ok (.JAL (storedImmediate ++ 0#1, sailRegister rd)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem jal_decoders_correspond (storedImmediate : BitVec 20)
    (rd : RV32I.Register) :
    DecodersCorrespondAt (generatedJalEncoding storedImmediate rd)
      (.JAL (storedImmediate ++ 0#1, sailRegister rd)) := by
  change generatedBaseView
      (.JAL (storedImmediate ++ 0#1, sailRegister rd)) =
    RV32I.Decoder.decode (generatedJalEncoding storedImmediate rd)
  rw [clean_decodes_generatedJalEncoding]
  simp [generatedBaseView]

/-- The actual generated decoder accepts every legal JALR field
combination, including all twelve-bit two's-complement immediates. -/
theorem generated_decodes_jalr (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedJalrEncoding immediate rs1 rd) sail =
      (.ok (.JALR (immediate, sailRegister rs1, sailRegister rd)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem jalr_decoders_correspond (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    DecodersCorrespondAt (generatedJalrEncoding immediate rs1 rd)
      (.JALR (immediate, sailRegister rs1, sailRegister rd)) := by
  change generatedBaseView
      (.JALR (immediate, sailRegister rs1, sailRegister rd)) =
    RV32I.Decoder.decode (generatedJalrEncoding immediate rs1 rd)
  rw [clean_decodes_generatedJalrEncoding]
  simp [generatedBaseView]

/-- The actual generated decoder accepts every BEQ field combination. -/
theorem generated_decodes_beq (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards
        (generatedBtypeEncoding storedImmediate rs2 rs1 .BEQ) sail =
      (.ok (.BTYPE (storedImmediate ++ 0#1, sailRegister rs2,
        sailRegister rs1, .BEQ)) sail : GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_bne (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards
        (generatedBtypeEncoding storedImmediate rs2 rs1 .BNE) sail =
      (.ok (.BTYPE (storedImmediate ++ 0#1, sailRegister rs2,
        sailRegister rs1, .BNE)) sail : GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_blt (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards
        (generatedBtypeEncoding storedImmediate rs2 rs1 .BLT) sail =
      (.ok (.BTYPE (storedImmediate ++ 0#1, sailRegister rs2,
        sailRegister rs1, .BLT)) sail : GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_bge (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards
        (generatedBtypeEncoding storedImmediate rs2 rs1 .BGE) sail =
      (.ok (.BTYPE (storedImmediate ++ 0#1, sailRegister rs2,
        sailRegister rs1, .BGE)) sail : GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_bltu (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards
        (generatedBtypeEncoding storedImmediate rs2 rs1 .BLTU) sail =
      (.ok (.BTYPE (storedImmediate ++ 0#1, sailRegister rs2,
        sailRegister rs1, .BLTU)) sail : GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_bgeu (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards
        (generatedBtypeEncoding storedImmediate rs2 rs1 .BGEU) sail =
      (.ok (.BTYPE (storedImmediate ++ 0#1, sailRegister rs2,
        sailRegister rs1, .BGEU)) sail : GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

/-- The complete legal B-type family, factored through the six generated
operation constructors so the large generated proof terms remain shallow. -/
theorem generated_decodes_btype (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards
        (generatedBtypeEncoding storedImmediate rs2 rs1 operation) sail =
      (.ok (.BTYPE (storedImmediate ++ 0#1, sailRegister rs2,
        sailRegister rs1, operation)) sail : GeneratedDecodeResult) := by
  cases operation
  · exact generated_decodes_beq storedImmediate rs2 rs1 sail profile
  · exact generated_decodes_bne storedImmediate rs2 rs1 sail profile
  · exact generated_decodes_blt storedImmediate rs2 rs1 sail profile
  · exact generated_decodes_bge storedImmediate rs2 rs1 sail profile
  · exact generated_decodes_bltu storedImmediate rs2 rs1 sail profile
  · exact generated_decodes_bgeu storedImmediate rs2 rs1 sail profile

theorem btype_decoders_correspond (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    DecodersCorrespondAt
      (generatedBtypeEncoding storedImmediate rs2 rs1 operation)
      (.BTYPE (storedImmediate ++ 0#1, sailRegister rs2,
        sailRegister rs1, operation)) := by
  cases operation <;>
    change generatedBaseView
        (.BTYPE (storedImmediate ++ 0#1, sailRegister rs2,
          sailRegister rs1, _)) =
      RV32I.Decoder.decode
        (generatedBtypeEncoding storedImmediate rs2 rs1 _) <;>
    rw [clean_decodes_generatedBtypeEncoding] <;>
    simp [generatedBaseView, cleanBranchInstruction]

/-- The two remaining branch `funct3` values are reserved by base RV32I.
These facts use the generated predicate which guards entry to its BTYPE
operand decoder.  They deliberately stop at that family boundary; proving the
eventual whole-decoder `ILLEGAL` fallback belongs to the later exhaustive
rejected-word classification. -/
theorem generated_btype_matcher_rejects_010 :
    encdec_bop_backwards_matches 0b010#3 = false := by
  rfl

theorem generated_btype_matcher_rejects_011 :
    encdec_bop_backwards_matches 0b011#3 = false := by
  rfl

/-! ## OP-IMM: ordinary I-type operations -/

/-- The generated platform hard-enables Zicbop and therefore refines three
base ORI-to-x0 HINT encodings into prefetch instructions before reaching its
ordinary ITYPE clause. -/
theorem generated_decodes_zicbop (upperImmediate : BitVec 7)
    (rs1 : RV32I.Register) (operation : LeanRV32D.cbop_zicbop)
    (sail : SailState) :
    encdec_backwards
        (generatedZicbopEncoding upperImmediate rs1 operation) sail =
      (.ok (.ZICBOP (operation, sailRegister rs1,
        upperImmediate ++ 0#5)) sail : GeneratedDecodeResult) := by
  cases operation <;> close_generated_decode rfl

theorem zicbop_decoders_correspond (upperImmediate : BitVec 7)
    (rs1 : RV32I.Register) (operation : LeanRV32D.cbop_zicbop) :
    DecodersCorrespondAt
      (generatedZicbopEncoding upperImmediate rs1 operation)
      (.ZICBOP (operation, sailRegister rs1, upperImmediate ++ 0#5)) := by
  cases operation <;>
    change generatedBaseView
        (.ZICBOP (_, sailRegister rs1, upperImmediate ++ 0#5)) =
      RV32I.Decoder.decode (generatedZicbopEncoding upperImmediate rs1 _) <;>
    rw [clean_decodes_generatedZicbopEncoding] <;>
    simp [generatedBaseView, encdec_cbop_zicbop_forwards] <;>
    bv_decide

theorem generated_decodes_addi (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedItypeEncoding immediate rs1 rd .ADDI) sail =
      (.ok (.ITYPE (immediate, sailRegister rs1, sailRegister rd, .ADDI)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_slti (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedItypeEncoding immediate rs1 rd .SLTI) sail =
      (.ok (.ITYPE (immediate, sailRegister rs1, sailRegister rd, .SLTI)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_sltiu (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedItypeEncoding immediate rs1 rd .SLTIU) sail =
      (.ok (.ITYPE (immediate, sailRegister rs1, sailRegister rd, .SLTIU)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_xori (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedItypeEncoding immediate rs1 rd .XORI) sail =
      (.ok (.ITYPE (immediate, sailRegister rs1, sailRegister rd, .XORI)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_ori (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail)
    (notPrefetch : ¬ ZicbopInterposes immediate rs1 rd) :
    encdec_backwards (generatedItypeEncoding immediate rs1 rd .ORI) sail =
      (.ok (.ITYPE (immediate, sailRegister rs1, sailRegister rd, .ORI)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

/-- Exhaustive generated-decoder result for the base ORI encoding space: the
word is either one of the three hard-enabled Zicbop HINT refinements or reaches
the ordinary ITYPE clause. -/
theorem generated_decodes_ori_partition (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    (∃ upperImmediate : BitVec 7,
      ∃ operation : LeanRV32D.cbop_zicbop,
        immediate = upperImmediate ++ encdec_cbop_zicbop_forwards operation ∧
        rd = 0 ∧
        encdec_backwards (generatedItypeEncoding immediate rs1 rd .ORI) sail =
          (.ok (.ZICBOP
            (operation, sailRegister rs1, upperImmediate ++ 0#5)) sail :
              GeneratedDecodeResult)) ∨
      encdec_backwards (generatedItypeEncoding immediate rs1 rd .ORI) sail =
        (.ok (.ITYPE
          (immediate, sailRegister rs1, sailRegister rd, .ORI)) sail :
            GeneratedDecodeResult) := by
  by_cases interposes : ZicbopInterposes immediate rs1 rd
  · rcases interposes.decompose with ⟨upperImmediate, operation, rdZero,
      immediateShape⟩
    left
    refine ⟨upperImmediate, operation, immediateShape, rdZero, ?_⟩
    subst rd
    subst immediate
    exact generated_decodes_zicbop upperImmediate rs1 operation sail
  · right
    exact generated_decodes_ori immediate rs1 rd sail profile interposes

theorem generated_decodes_andi (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedItypeEncoding immediate rs1 rd .ANDI) sail =
      (.ok (.ITYPE (immediate, sailRegister rs1, sailRegister rd, .ANDI)) sail :
        GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_itype (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.iop)
    (sail : SailState) (profile : BaseDecoderProfile sail)
    (notPrefetch : operation = .ORI →
      ¬ ZicbopInterposes immediate rs1 rd) :
    encdec_backwards (generatedItypeEncoding immediate rs1 rd operation) sail =
      (.ok (.ITYPE (immediate, sailRegister rs1, sailRegister rd, operation))
        sail : GeneratedDecodeResult) := by
  cases operation
  · exact generated_decodes_addi immediate rs1 rd sail profile
  · exact generated_decodes_slti immediate rs1 rd sail profile
  · exact generated_decodes_sltiu immediate rs1 rd sail profile
  · exact generated_decodes_xori immediate rs1 rd sail profile
  · exact generated_decodes_ori immediate rs1 rd sail profile
      (notPrefetch rfl)
  · exact generated_decodes_andi immediate rs1 rd sail profile

theorem itype_decoders_correspond (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.iop) :
    DecodersCorrespondAt (generatedItypeEncoding immediate rs1 rd operation)
      (.ITYPE (immediate, sailRegister rs1, sailRegister rd, operation)) := by
  cases operation <;>
    change generatedBaseView
        (.ITYPE (immediate, sailRegister rs1, sailRegister rd, _)) =
      RV32I.Decoder.decode (generatedItypeEncoding immediate rs1 rd _) <;>
    rw [clean_decodes_generatedItypeEncoding] <;>
    simp [generatedBaseView, cleanItypeInstruction]

/-! ## OP-IMM: RV32 shift-immediate operations -/

theorem generated_decodes_slli (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedShiftEncoding shamt rs1 rd .SLLI) sail =
      (.ok (.SHIFTIOP (0#1 ++ shamt, sailRegister rs1, sailRegister rd,
        .SLLI)) sail : GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_srli (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedShiftEncoding shamt rs1 rd .SRLI) sail =
      (.ok (.SHIFTIOP (0#1 ++ shamt, sailRegister rs1, sailRegister rd,
        .SRLI)) sail : GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_srai (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedShiftEncoding shamt rs1 rd .SRAI) sail =
      (.ok (.SHIFTIOP (0#1 ++ shamt, sailRegister rs1, sailRegister rd,
        .SRAI)) sail : GeneratedDecodeResult) := by
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_shift_itype (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedShiftEncoding shamt rs1 rd operation) sail =
      (.ok (.SHIFTIOP (0#1 ++ shamt, sailRegister rs1, sailRegister rd,
        operation)) sail : GeneratedDecodeResult) := by
  cases operation
  · exact generated_decodes_slli shamt rs1 rd sail profile
  · exact generated_decodes_srli shamt rs1 rd sail profile
  · exact generated_decodes_srai shamt rs1 rd sail profile

theorem shift_itype_decoders_correspond (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop) :
    DecodersCorrespondAt (generatedShiftEncoding shamt rs1 rd operation)
      (.SHIFTIOP (0#1 ++ shamt, sailRegister rs1, sailRegister rd,
        operation)) := by
  have amountInRange : (0#1 ++ shamt).toNat < 32 := by
    rw [BitVec.toNat_append]
    simpa using shamt.isLt
  have truncateAmount : BitVec.setWidth 5 (0#1 ++ shamt) = shamt := by
    bv_decide
  cases operation <;>
    change generatedBaseView
        (.SHIFTIOP (0#1 ++ shamt, sailRegister rs1, sailRegister rd, _)) =
      RV32I.Decoder.decode (generatedShiftEncoding shamt rs1 rd _) <;>
    rw [clean_decodes_generatedShiftEncoding] <;>
    simp [generatedBaseView, cleanShiftInstruction, amountInRange,
      truncateAmount]

/-- The ordinary ITYPE clause excludes the two `funct3` values reserved for
the later shift clauses. -/
theorem generated_itype_matcher_rejects_shift_left :
    encdec_iop_backwards_matches 0b001#3 = false := by
  rfl

theorem generated_itype_matcher_rejects_shift_right :
    encdec_iop_backwards_matches 0b101#3 = false := by
  rfl

/-! ## OP / RTYPE -/

/-- The earlier hard-enabled Zihintntl clause recognizes all four NTL
refinements symbolically, not merely as four concrete regression words. -/
theorem generated_decodes_ntl (operation : LeanRV32D.ntl_type)
    (sail : SailState) :
    encdec_backwards (generatedNtlEncoding operation) sail =
      (.ok (.NTL operation) sail : GeneratedDecodeResult) := by
  close_generated_decode rfl

/-- Ordinary ADD reaches Sail's base RTYPE clause exactly when the earlier
NTL refinement does not interpose. -/
theorem generated_decodes_add (rs2 rs1 rd : RV32I.Register)
    (sail : SailState) (profile : BaseDecoderProfile sail)
    (notNtl : ¬ NtlInterposes rs2 rs1 rd) :
    encdec_backwards (generatedRtypeEncoding rs2 rs1 rd .ADD) sail =
      (.ok (.RTYPE (sailRegister rs2, sailRegister rs1, sailRegister rd,
        .ADD)) sail : GeneratedDecodeResult) := by
  have ntlGuard :
      ¬ ((encdec_ntl_backwards_matches
            (Sail.BitVec.extractLsb
              (generatedRtypeEncoding rs2 rs1 rd .ADD) 24 20) &&
          ((Sail.BitVec.extractLsb
                (generatedRtypeEncoding rs2 rs1 rd .ADD) 31 25 ==
              0b0000000#7) &&
            (Sail.BitVec.extractLsb
                (generatedRtypeEncoding rs2 rs1 rd .ADD) 19 0 ==
              0x00033#20))) = true) := by
    simpa only [NtlInterposes] using notNtl
  show encdec_backwards (generatedRtypeEncoding rs2 rs1 rd .ADD) sail =
    (.ok (.RTYPE (sailRegister rs2, sailRegister rs1, sailRegister rd,
      .ADD)) sail : GeneratedDecodeResult)
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_slt (rs2 rs1 rd : RV32I.Register)
    (sail : SailState) (profile : BaseDecoderProfile sail) :
    encdec_backwards (generatedRtypeEncoding rs2 rs1 rd .SLT) sail =
      (.ok (.RTYPE (sailRegister rs2, sailRegister rs1, sailRegister rd,
        .SLT)) sail : GeneratedDecodeResult) := by
  have ntlGuard := generatedRtype_ntl_guard_false rs2 rs1 rd .SLT (by
    intro impossible
    cases impossible)
  show encdec_backwards (generatedRtypeEncoding rs2 rs1 rd .SLT) sail =
    (.ok (.RTYPE (sailRegister rs2, sailRegister rs1, sailRegister rd,
      .SLT)) sail : GeneratedDecodeResult)
  close_generated_decode profile.zicfilpDisabled

theorem generated_decodes_ntl_p1 (sail : SailState) :
    encdec_backwards 0x00200033 sail =
      (.ok (.NTL .NTL_P1) sail : GeneratedDecodeResult) := by
  close_concrete_generated_decode rfl

theorem generated_decodes_ntl_pall (sail : SailState) :
    encdec_backwards 0x00300033 sail =
      (.ok (.NTL .NTL_PALL) sail : GeneratedDecodeResult) := by
  close_concrete_generated_decode rfl

theorem generated_decodes_ntl_s1 (sail : SailState) :
    encdec_backwards 0x00400033 sail =
      (.ok (.NTL .NTL_S1) sail : GeneratedDecodeResult) := by
  close_concrete_generated_decode rfl

theorem generated_decodes_ntl_all (sail : SailState) :
    encdec_backwards 0x00500033 sail =
      (.ok (.NTL .NTL_ALL) sail : GeneratedDecodeResult) := by
  close_concrete_generated_decode rfl

theorem generated_decodes_pause (sail : SailState) :
    encdec_backwards 0x0100000f sail =
      (.ok (.PAUSE ()) sail : GeneratedDecodeResult) := by
  close_concrete_generated_decode rfl

theorem generated_decodes_fence_tso (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards 0x8330000f sail =
      (.ok (.FENCE_TSO ()) sail : GeneratedDecodeResult) := by
  close_concrete_generated_decode profile.zicfilpDisabled

theorem generated_decodes_ecall (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards 0x00000073 sail =
      (.ok (.ECALL ()) sail : GeneratedDecodeResult) := by
  close_concrete_generated_decode profile.zicfilpDisabled

theorem generated_decodes_ebreak (sail : SailState)
    (profile : BaseDecoderProfile sail) :
    encdec_backwards 0x00100073 sail =
      (.ok (.EBREAK ()) sail : GeneratedDecodeResult) := by
  close_concrete_generated_decode profile.zicfilpDisabled

theorem ntl_p1_decoders_correspond :
    DecodersCorrespondAt 0x00200033 (.NTL .NTL_P1) := by
  rfl

theorem ntl_pall_decoders_correspond :
    DecodersCorrespondAt 0x00300033 (.NTL .NTL_PALL) := by
  rfl

theorem ntl_s1_decoders_correspond :
    DecodersCorrespondAt 0x00400033 (.NTL .NTL_S1) := by
  rfl

theorem ntl_all_decoders_correspond :
    DecodersCorrespondAt 0x00500033 (.NTL .NTL_ALL) := by
  rfl

theorem pause_decoders_correspond :
    DecodersCorrespondAt 0x0100000f (.PAUSE ()) := by
  rfl

theorem fence_tso_decoders_correspond :
    DecodersCorrespondAt 0x8330000f (.FENCE_TSO ()) := by
  rfl

theorem ecall_decoders_correspond :
    DecodersCorrespondAt 0x00000073 (.ECALL ()) := by
  rfl

theorem ebreak_decoders_correspond :
    DecodersCorrespondAt 0x00100073 (.EBREAK ()) := by
  rfl

end RV32I.SailBridge
