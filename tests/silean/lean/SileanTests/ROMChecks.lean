import Silean.Authoring.ModuleDesign
import Silean.FIRRTL
import Silean.Modules.ROM.ROMDerived

namespace SileanTests.ROM

open Silean Silean.FIRRTL
open Silean.Authoring
open Silean.Modules

def contents : Fin (Modules.ROM.entryCount 2) → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => false

def otherContents : Fin (Modules.ROM.entryCount 2) → Bool
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => true

def shortContents : Fin (Modules.ROM.entryCount 1) → Bool
  | 0 => false
  | 1 => true

def singletonContents : Fin (Modules.ROM.entryCount 0) → Bool
  | 0 => true

def wordType : SignalType := .vector 2 .bit

def wordContents : Fin (Modules.ROM.entryCount 2) → wordType.Denote
  | 0 => fun | 0 => false | 1 => false
  | 1 => fun | 0 => true | 1 => false
  | 2 => fun | 0 => false | 1 => true
  | 3 => fun | 0 => true | 1 => true

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.ROM.ports .bit 2) :=
  Modules.ROM.certified "lookup_table" .bit 2 contents

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.ROM.ports .bit 0) :=
  Modules.ROM.certified "singleton" .bit 0 singletonContents

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.ROM.ports wordType 2) :=
  Modules.ROM.certified "word_table" wordType 2 wordContents

example : Contracts.Cycle.Implements
    (Modules.ROM.moduleStructure "lookup_table" .bit 2 contents)
    (Modules.ROM.cycleContract .bit 2 contents)
    (Modules.ROM.certification "lookup_table" .bit 2 contents).stateCorresponds :=
  Modules.ROM.implements_contract "lookup_table" .bit 2 contents

example :
    (Modules.ROM.naming "lookup_table" .bit 2 contents).key =
      { family := "ROM"
        variant := "lookup_table"
        specialization := [.signalType .bit, .natural 2] } :=
  rfl

-- Element shape and address width are part of the emitted definition identity.
example :
    (Modules.ROM.naming "same_name" .bit 2 contents).key ≠
      (Modules.ROM.naming "same_name" .bit 1 shortContents).key := by
  decide

#check Modules.ROM.place
#check Modules.ROM.placeNamed

example :
    (Modules.ROM.naming "same_name" .bit 2 contents).key ≠
      (Modules.ROM.naming "same_name" wordType 2 wordContents).key := by
  decide

namespace PairBoundary

module_ports ports where
  input address : .vector 2 .bit,
  output first : .bit,
  output second : .bit

end PairBoundary

module_design IdenticalPair where
  boundary (PairBoundary.ports)
    (naming := PairBoundary.Naming.ports)
  instances {
    firstROM := Modules.ROM.design "shared_table" .bit 2 contents,
    secondROM := Modules.ROM.design "shared_table" .bit 2 contents }
  wiring {
    outputs {
      .first := firstROM.data,
      .second := secondROM.data }
    instance (.firstROM) {
      .address := input.address }
    instance (.secondROM) {
      .address := input.address }
  }

module_design ConflictingPair where
  boundary (PairBoundary.ports)
    (naming := PairBoundary.Naming.ports)
  instances {
    firstROM := Modules.ROM.design "conflicting_table" .bit 2 contents,
    secondROM := Modules.ROM.design "conflicting_table" .bit 2 otherContents }
  wiring {
    outputs {
      .first := firstROM.data,
      .second := secondROM.data }
    instance (.firstROM) {
      .address := input.address }
    instance (.secondROM) {
      .address := input.address }
  }

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occursExactlyOnce (text fragment : String) : Bool :=
  (text.splitOn fragment).length = 2

#guard match renderCircuit
    (Modules.ROM.naming "lookup_table" .bit 2 contents) with
  | .error _ => false
  | .ok text => [
      "public module ROM_lookup_table_bit_2",
      "input address : UInt<1>[2]",
      "output data : UInt<1>",
      "inst contents",
      "inst select",
      "connect select.values, contents.value",
      "connect select.index, address"].all (contains text)

#guard match renderCircuit
    (Modules.ROM.naming "singleton" .bit 0 singletonContents) with
  | .error _ => false
  | .ok text => ["public module ROM_singleton_bit_0",
      "input address : UInt<1>[0]", "output data : UInt<1>"].all
      (contains text)

#guard match renderCircuit
    (Modules.ROM.naming "word_table" wordType 2 wordContents) with
  | .error _ => false
  | .ok text => ["public module ROM_word_table_v2_bit_2",
      "output data : UInt<1>[2]"].all (contains text)

-- Repeated uses of the same named table share one emitted definition.
#guard match renderCircuit IdenticalPair.naming with
  | .error _ => false
  | .ok text => occursExactlyOnce text "module ROM_shared_table_bit_2 :"

-- Reusing one definition identity for different contents is rejected.
#guard match renderCircuit ConflictingPair.naming with
  | .ok _ => false
  | .error message => contains message
      "module key 'ROM_conflicting_table_bit_2' names two different FIRRTL definitions"

end SileanTests.ROM
