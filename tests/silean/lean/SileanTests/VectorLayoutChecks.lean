import Silean.FIRRTL
import Silean.Modules.VectorLayout.VectorLayoutTheorems

namespace SileanTests.VectorLayout

open Silean
open Silean.Modules.VectorLayout

def input4 : Fin 4 → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => false

def reverse : Fin 4 → BitSource 4
  | 0 => .input 3
  | 1 => .input 2
  | 2 => .input 1
  | 3 => .input 0

def duplicate : Fin 4 → BitSource 2
  | 0 | 1 => .input 0
  | 2 | 3 => .input 1

def truncate : Fin 2 → BitSource 4
  | 0 => .input 1
  | 1 => .input 2

def signExtend : Fin 4 → BitSource 2
  | 0 => .input 0
  | 1 | 2 | 3 => .input 1

def insertConstants : Fin 4 → BitSource 2
  | 0 => .constant false
  | 1 => .input 0
  | 2 => .input 1
  | 3 => .constant true

/-- The PicoRV32 J-immediate layout that motivated the generic module. -/
def immediateJ : Fin 32 → BitSource 32 := fun index =>
  if zero : index.val = 0 then .constant false
  else if low : index.val ≤ 10 then .input ⟨index.val + 20, by omega⟩
  else if eleven : index.val = 11 then .input ⟨20, by omega⟩
  else if middle : index.val ≤ 19 then .input index
  else .input ⟨31, by omega⟩

#guard apply reverse input4 0 == false
#guard apply reverse input4 1 == true
#guard apply reverse input4 2 == true
#guard apply reverse input4 3 == false

#guard apply duplicate (fun index => index == 1) 0 == false
#guard apply duplicate (fun index => index == 1) 1 == false
#guard apply duplicate (fun index => index == 1) 2 == true
#guard apply duplicate (fun index => index == 1) 3 == true

#guard apply truncate input4 0 == true
#guard apply truncate input4 1 == true

#guard apply signExtend (fun index => index == 1) 0 == false
#guard apply signExtend (fun index => index == 1) 1 == true
#guard apply signExtend (fun index => index == 1) 3 == true

#guard apply insertConstants (fun index => index == 1) 0 == false
#guard apply insertConstants (fun index => index == 1) 1 == false
#guard apply insertConstants (fun index => index == 1) 2 == true
#guard apply insertConstants (fun index => index == 1) 3 == true

#guard apply immediateJ (fun index => index.val == 31) 0 == false
#guard apply immediateJ (fun index => index.val == 31) 31 == true

#guard variant reverse !=
  variant (fun _ : Fin 4 => (BitSource.constant false : BitSource 4))

#guard match Silean.FIRRTL.renderCircuit (design 2 4 insertConstants).naming with
  | .ok _ => true
  | .error _ => false

noncomputable example : Contracts.Cycle.ModuleCycleCertification
    (moduleStructure 2 4 insertConstants)
    (cycleContract 2 4 insertConstants) :=
  certification 2 4 insertConstants

def inputs : (ports 2 4).inputs.Values
  | .input => fun index => index == 1

def evaluatedOutput :=
  ((cycleContract 2 4 insertConstants).evaluate
    inputs SignalMap.emptyValues).1 .output

#guard !evaluatedOutput 0
#guard !evaluatedOutput 1
#guard evaluatedOutput 2
#guard evaluatedOutput 3

end SileanTests.VectorLayout
