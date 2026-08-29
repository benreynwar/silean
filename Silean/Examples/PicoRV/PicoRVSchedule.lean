import Silean.Examples.PicoRV.PicoRV

namespace Silean.Examples.PicoRV.PicoRV

open Silean Silean.Contracts.Cycle.Certification

/-! The schedule witnesses below establish a topological order for the
blackbox contracts. They are proof inputs, not execution order stored in the
module structure. -/

private abbrev controlOutputs : RuleOccurrence children := ⟨.control, .outputs⟩
private abbrev decoderOutputs : RuleOccurrence children := ⟨.decoder, .outputs⟩
private abbrev datapathRegistered : RuleOccurrence children := ⟨.datapath, .registered⟩
private abbrev memoryRegistered : RuleOccurrence children := ⟨.mem, .registered⟩
private abbrev memoryRdataQ : RuleOccurrence children := ⟨.mem, .memRdataQ⟩
private abbrev regsRs1 : RuleOccurrence children := ⟨.cpuregs, .cpuregs_rs1⟩
private abbrev regsRs2 : RuleOccurrence children := ⟨.cpuregs, .cpuregs_rs2⟩
private abbrev datapathNextPc : RuleOccurrence children := ⟨.datapath, .nextPc⟩
private abbrev datapathComparison : RuleOccurrence children := ⟨.datapath, .comparison⟩
private abbrev datapathWriteback : RuleOccurrence children := ⟨.datapath, .writeback⟩
private abbrev memoryLaRead : RuleOccurrence children := ⟨.mem, .memLaRead⟩
private abbrev memoryLaWrite : RuleOccurrence children := ⟨.mem, .memLaWrite⟩
private abbrev memoryLaAddr : RuleOccurrence children := ⟨.mem, .memLaAddr⟩
private abbrev memoryLaWdata : RuleOccurrence children := ⟨.mem, .memLaWdata⟩
private abbrev memoryLaWstrb : RuleOccurrence children := ⟨.mem, .memLaWstrb⟩
private abbrev memoryDone : RuleOccurrence children := ⟨.mem, .memDone⟩
private abbrev memoryRdataWord : RuleOccurrence children := ⟨.mem, .memRdataWord⟩
private abbrev memoryRdataLatched : RuleOccurrence children := ⟨.mem, .memRdataLatched⟩

private local instance : DecidableEq (RuleOccurrence children) :=
  RuleOccurrence.decidableEq

private theorem controlOutputAvailable {available : Availability children}
    (called : controlOutputs ∈ available) (output : Control.Output) :
    sourceAvailable (fun _ : Input => True) available
      (context.instanceOutput Instance.control output) := by
  apply sourceAvailable_instanceOutput called
  change output ∈ Control.outputMap.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact ListIndex.get_eq (Control.outputMap.labels.locate output) ▸ List.get_mem _ _

private theorem decoderOutputAvailable {available : Availability children}
    (called : decoderOutputs ∈ available) (output : Decoder.Output) :
    sourceAvailable (fun _ : Input => True) available
      (context.instanceOutput Instance.decoder output) := by
  apply sourceAvailable_instanceOutput called
  change output ∈ Decoder.outputMap.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact ListIndex.get_eq (Decoder.outputMap.labels.locate output) ▸ List.get_mem _ _

/-! Invoke every child output rule in dependency order. The polymorphic finish
condition lets the same generic witness establish complete rule coverage,
child-state readiness, or availability of a selected parent output. -/
private noncomputable def completeSchedule :
    Schedule body children (fun _ => True) (CoversAllRules children) [] :=
  .call controlOutputs (by intro input h; simp [RuleOccurrence.reads, Control.outputRule, SignalSelection.labels] at h) (by decide)
  (.call decoderOutputs (by intro input h; simp [RuleOccurrence.reads, Decoder.outputRule, SignalSelection.labels] at h) (by decide)
  (.call datapathRegistered (by intro input h; simp [RuleOccurrence.reads, Datapath.registeredRule, SignalSelection.labels] at h) (by decide)
  (.call memoryRegistered (by intro input h; simp [RuleOccurrence.reads, Memory.registeredRule, SignalSelection.labels] at h) (by decide)
  (.call memoryRdataQ (by intro input h; simp [RuleOccurrence.reads, Memory.memRdataQRule, SignalSelection.labels] at h) (by decide)
  (.call regsRs1 (by
    intro input h
    have equal : input = .decoded_rs1 := by
      simpa [RuleOccurrence.reads, Regs.cpuregsRs1Rule, SignalMap.select,
        SignalSelection.labels] using h
    subst input
    exact decoderOutputAvailable (by simp) .decoded_rs1) (by decide)
  (.call regsRs2 (by
    intro input h
    have equal : input = .decoded_rs2 := by
      simpa [RuleOccurrence.reads, Regs.cpuregsRs2Rule, SignalMap.select,
        SignalSelection.labels] using h
    subst input
    exact decoderOutputAvailable (by simp) .decoded_rs2) (by decide)
  (.call datapathNextPc (by
    intro input h
    cases input <;> simp_all [RuleOccurrence.reads, Datapath.nextPcRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> exact controlOutputAvailable (by simp) _) (by decide)
  (.call datapathComparison
    (by
      intro input h
      cases input <;> simp_all [RuleOccurrence.reads, Datapath.comparisonRule,
        SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
        <;> exact decoderOutputAvailable (by simp) _) (by decide)
  (.call datapathWriteback
    (by
      intro input h
      cases input <;> simp_all [RuleOccurrence.reads, Datapath.writebackRule,
        SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
        <;> exact controlOutputAvailable (by simp) _) (by decide)
  (.call memoryLaRead (by
    intro input h
    cases input <;> simp_all [RuleOccurrence.reads, Memory.memLaReadRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first | exact trivial | exact controlOutputAvailable (by simp) _) (by decide)
  (.call memoryLaWrite (by
    intro input h
    cases input <;> simp_all [RuleOccurrence.reads, Memory.memLaWriteRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first | exact trivial | exact controlOutputAvailable (by simp) _) (by decide)
  (.call memoryLaAddr (by
    intro input h
    cases input <;> simp_all [RuleOccurrence.reads, Memory.memLaAddrRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first
        | exact controlOutputAvailable (by simp) _
        | exact sourceAvailable_instanceOutput (body := body) (children := children)
            (child := Instance.datapath)
            (rule := Datapath.Rule.nextPc) (output := Datapath.Output.next_pc)
            (by simp) (by simp [RuleOccurrence.writes, Datapath.nextPcRule,
              SignalMap.select, SignalSelection.labels])
        | exact sourceAvailable_instanceOutput (body := body) (children := children)
            (child := Instance.datapath)
            (rule := Datapath.Rule.registered) (output := Datapath.Output.reg_op1)
            (by simp) (by simp [RuleOccurrence.writes, Datapath.registeredRule,
              SignalMap.select, SignalSelection.prepend, SignalSelection.labels])) (by decide)
  (.call memoryLaWdata (by
    intro input h
    cases input <;> simp_all [RuleOccurrence.reads, Memory.memLaWdataRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first
        | exact controlOutputAvailable (by simp) _
        | exact sourceAvailable_instanceOutput (body := body) (children := children)
            (child := Instance.datapath)
            (rule := Datapath.Rule.registered) (output := Datapath.Output.reg_op2)
            (by simp) (by simp [RuleOccurrence.writes, Datapath.registeredRule,
              SignalMap.select, SignalSelection.prepend, SignalSelection.labels])) (by decide)
  (.call memoryLaWstrb (by
    intro input h
    cases input <;> simp_all [RuleOccurrence.reads, Memory.memLaWstrbRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first
        | exact controlOutputAvailable (by simp) _
        | exact sourceAvailable_instanceOutput (body := body) (children := children)
            (child := Instance.datapath)
            (rule := Datapath.Rule.registered) (output := Datapath.Output.reg_op1)
            (by simp) (by simp [RuleOccurrence.writes, Datapath.registeredRule,
              SignalMap.select, SignalSelection.prepend, SignalSelection.labels])) (by decide)
  (.call memoryDone (by
    intro input h
    cases input <;> simp_all [RuleOccurrence.reads, Memory.memDoneRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first | exact trivial | exact controlOutputAvailable (by simp) _) (by decide)
  (.call memoryRdataWord
    (by
      intro input h
      cases input <;> simp_all [RuleOccurrence.reads, Memory.memRdataWordRule,
        SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
        <;> first
          | exact trivial
          | exact controlOutputAvailable (by simp) _
          | exact sourceAvailable_instanceOutput (body := body) (children := children)
              (child := Instance.datapath)
              (rule := Datapath.Rule.registered) (output := Datapath.Output.reg_op1)
              (by simp) (by simp [RuleOccurrence.writes, Datapath.registeredRule,
                SignalMap.select, SignalSelection.prepend, SignalSelection.labels])) (by decide)
  (.call memoryRdataLatched
    (by
      intro input h
      cases input <;> simp_all [RuleOccurrence.reads, Memory.memRdataLatchedRule,
        SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
        <;> exact trivial) (by decide)
  (.done (by
    intro child rule
    cases child <;> cases rule <;> simp [controlOutputs, decoderOutputs,
      datapathRegistered, memoryRegistered, memoryRdataQ, regsRs1, regsRs2,
      datapathNextPc, datapathComparison, datapathWriteback, memoryLaRead,
      memoryLaWrite, memoryLaAddr, memoryLaWdata, memoryLaWstrb, memoryDone,
      memoryRdataWord, memoryRdataLatched])))))))))))))))))))

noncomputable def allRulesSchedule :
    Schedule body children (fun _ => True) (CoversAllRules children) [] :=
  completeSchedule

noncomputable def stateSchedule : StateSchedule body children :=
  completeSchedule.mapFinish fun _available covers child input _ =>
    sourceAvailable_of_covers covers (body.wiring.instanceInput child input)

abbrev ParentOutputSchedule (output : Output) :=
  Schedule body children (fun _ => True)
    (fun available => sourceAvailable (fun _ => True) available
      (body.wiring.moduleOutput output)) []

noncomputable def outputSchedule (output : Output) : ParentOutputSchedule output :=
  completeSchedule.mapFinish fun _available covers =>
    sourceAvailable_of_covers covers (body.wiring.moduleOutput output)

theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution := by
  apply allRulesSchedule.hasAtMostOneSolution (fun _ => trivial)
  exact allRulesSchedule.finished

end Silean.Examples.PicoRV.PicoRV
