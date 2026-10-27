import Silean2.FoundationsH
import Silean2.CIRCTH

namespace Silean2.Modules.Extract

open Silean2.Foundations
open Silean2.CIRCT

structure ExtractParams where
  inputWidth : Nat
  lowBit : Nat
  outputWidth : Nat
  inBounds : lowBit + outputWidth ≤ inputWidth


def ExtractParams.ParamsType : RawParamsType := params%[
  "inputWidth" : .nat,
  "lowBit" : .nat,
  "outputWidth" : .nat,
]

def ExtractParams.encode (p : ExtractParams) : ExtractParams.ParamsType.Denote :=
  (p.inputWidth, (p.lowBit, (p.outputWidth, ())))

def ExtractParams.decode (p : ExtractParams.ParamsType.Denote) : Except String ExtractParams :=
  let inputWidth : Nat := p.1
  let lowBit : Nat := p.2.1
  let outputWidth : Nat := p.2.2.1
  if h : lowBit + outputWidth ≤ inputWidth then
    pure { inputWidth := inputWidth, lowBit := lowBit, outputWidth := outputWidth, inBounds := h}
  else
    throw s!"Need lowBit + outputWidth ≤ inputwidth : {lowBit} + {outputWidth} ≤ {inputWidth}"

abbrev extractPorts (p : ExtractParams) : ModulePorts :=
  {
    nInputs := 1
    nOutputs := 1
    inputTypes := fun _ => .vector p.inputWidth .bit
    outputTypes := fun _ => .vector p.outputWidth .bit
  }

@[match_pattern]
abbrev source (p: ExtractParams): (extractPorts p).InputKey := ⟨0, by simp⟩
abbrev result (p: ExtractParams): (extractPorts p).OutputKey := ⟨0, by simp⟩

def extractFunction
    (p : ExtractParams)
    (inputs : (extractPorts p).InputValues)
    : (extractPorts p).OutputValues :=
  let source : Vector Bool p.inputWidth := inputs (source p)
  have h : min (p.lowBit + p.outputWidth) p.inputWidth  - p.lowBit = p.outputWidth := by
    simp [p.inBounds]
  let resultAlmost := source.extract p.lowBit (p.lowBit + p.outputWidth)
  let result : Vector Bool p.outputWidth := h ▸ resultAlmost
  fun _ => result

def extractSpec (p : ExtractParams) := Spec.ofFunction (extractFunction p)

def extractBuilder (p : ExtractParams) : CIRCTModuleBuilder (extractPorts p) :=
  fun inputs => do
    let result ← CIRCTBuilder.addExpr "result"
      (.extract (inputs (Extract.source p)) p.lowBit p.outputWidth p.inBounds)
    return fun _ => .exprRef result

def extractImpl (p : ExtractParams) (_ : CIRCTSettings)
    : CIRCTImplementation (extractPorts p) :=
  .primitive (extractBuilder p)

def extractName := "Extract"

def extractRegistration : ModuleRegistration := {
  rawParamsType := ExtractParams.ParamsType
  ParamsType := ExtractParams
  decodeParams := ExtractParams.decode
  ports := extractPorts
  impl := extractImpl
}

def extractRef (p : ExtractParams) : ModuleRef (extractPorts p) := {
  name := extractName,
  paramsType := ExtractParams.ParamsType,
  params := p.encode
}

end Silean2.Modules.Extract
