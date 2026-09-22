import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector
import Silean.Modules.ConditionalNegate.ConditionalNegateDerived
import Silean.Modules.UnsignedMultiply.UnsignedMultiplyDerived
import Silean.Modules.VectorLayout.VectorLayoutDerived

/-! # Full-width signed multiplication

`SignedMultiply` interprets two independently sized vectors as two's-complement
integers and returns their product at the combined width. This file contains
only the public boundary and natural contract; magnitude conversion, unsigned
multiplication, and conditional negation belong to the later hardware
structure rather than this specification.
-/

namespace Silean.Modules.SignedMultiply

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

module_ports ports (leftWidth : Nat) (rightWidth : Nat) where
  input left : .vector leftWidth .bit,
  input right : .vector rightWidth .bit,
  output result : .vector (leftWidth + rightWidth) .bit

/-- The full-width two's-complement representation of the signed product. -/
def resultValue (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    Fin (leftWidth + rightWidth) → Bool :=
  BitVector.ofBitVec <|
    BitVec.ofInt (leftWidth + rightWidth)
      ((BitVector.toBitVec leftWidth left).toInt *
        (BitVector.toBitVec rightWidth right).toInt)

module_cycle_contract cycleContract (leftWidth : Nat) (rightWidth : Nat)
    for ports leftWidth rightWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right]
    writes := {
      result := resultValue leftWidth rightWidth left right }
  state_rule where
    reads := []
    next := {}

/-- Select the most-significant bit, using false as the sign of the unique
zero-width value. -/
def signLayout (width : Nat) : Fin 1 → VectorLayout.BitSource width :=
  fun _ =>
    if positive : 0 < width then
      .input ⟨width - 1, by omega⟩
    else
      .constant false

open ports

/-- Readable sign/magnitude implementation of full-width signed
multiplication. -/
noncomputable def construction (leftWidth rightWidth : Nat) :
    ModuleBuilder (ports leftWidth rightWidth) Unit := do
  let left ← input leftWidth rightWidth .left
  let right ← input leftWidth rightWidth .right

  let leftSignVector ← VectorLayout.place (signLayout leftWidth) left
  let leftSignBits ← split (.vector 1 .bit) leftSignVector
  let leftSign := leftSignBits 0
  let rightSignVector ← VectorLayout.place (signLayout rightWidth) right
  let rightSignBits ← split (.vector 1 .bit) rightSignVector
  let rightSign := rightSignBits 0

  let leftMagnitude ← ConditionalNegate.place left leftSign
  let rightMagnitude ← ConditionalNegate.place right rightSign
  wire productNegate ← leftSign ^^^ rightSign
  let magnitudeProduct ← UnsignedMultiply.place
    leftMagnitude.result rightMagnitude.result
  let result ← ConditionalNegate.place magnitudeProduct productNegate
  output leftWidth rightWidth .result result.result

noncomputable def description (leftWidth rightWidth : Nat) : Description :=
  ModuleBuilder.build (Naming.ports leftWidth rightWidth)
    (construction leftWidth rightWidth)

end Silean.Modules.SignedMultiply
