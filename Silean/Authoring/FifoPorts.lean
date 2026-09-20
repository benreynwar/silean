import Silean.Authoring.CircuitDescription
import Silean.Interfaces.FifoPorts

/-! Typed authoring operations for the canonical FIFO boundary. -/

namespace Silean.Interfaces.Fifo.ports

open Silean
open Silean.Authoring.CircuitDescription

def input (element : SignalType) (port : (Fifo.ports element).inputs.Label) :
    ModuleBuilder (Fifo.ports element)
      (Net ((Fifo.ports element).inputs.signalType port)) :=
  ModuleBuilder.input (ports := Fifo.ports element) port

def output (element : SignalType) (port : (Fifo.ports element).outputs.Label)
    (net : Net ((Fifo.ports element).outputs.signalType port)) :
    ModuleBuilder (Fifo.ports element) Unit :=
  ModuleBuilder.output (ports := Fifo.ports element) port net

structure OutputNets (element : SignalType) where
  outputValid : Net .bit
  outputData : Net element
  inputReady : Net .bit

def OutputNets.ofFn (element : SignalType)
    (outputs : (port : (Fifo.ports element).outputs.Label) →
      Net ((Fifo.ports element).outputs.signalType port)) : OutputNets element :=
  ⟨outputs .outputValid, outputs .outputData, outputs .inputReady⟩

noncomputable def placeNamed (element : SignalType)
    (name : Naming.SourceName)
    (moduleStructure : ModuleStructure (Fifo.ports element))
    (naming : Naming.ModuleNaming moduleStructure)
    (inputValid : Net .bit) (inputData : Net element)
    (outputReady reset : Net .bit) : Builder (OutputNets element) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    { ports := Fifo.ports element, moduleStructure, naming } fun
      | .inputValid => inputValid
      | .inputData => inputData
      | .outputReady => outputReady
      | .reset => reset
  pure (OutputNets.ofFn element child)

noncomputable def placeIndexed (element : SignalType) (stem : String)
    (moduleStructure : ModuleStructure (Fifo.ports element))
    (naming : Naming.ModuleNaming moduleStructure)
    (inputValid : Net .bit) (inputData : Net element)
    (outputReady reset : Net .bit) : Builder (OutputNets element) := do
  let child ← Authoring.CircuitDescription.placeIndexed stem
    { ports := Fifo.ports element, moduleStructure, naming } fun
      | .inputValid => inputValid
      | .inputData => inputData
      | .outputReady => outputReady
      | .reset => reset
  pure (OutputNets.ofFn element child)

attribute [circuit_description]
  input output OutputNets.ofFn placeNamed placeIndexed

end Silean.Interfaces.Fifo.ports
