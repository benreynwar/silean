import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Equality.Equality
import Silean.Modules.Mux.Mux
import Silean.Modules.RegisterBank.RegisterBank
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.And
import Silean.Primitives.Not

/-! Expanded typed hierarchy for the PicoRV integer register file.

The reader-facing circuit and exact cycle contract live in `PicoRV/Regs.lean`.
This file keeps the representation needed by structural verification and
emission out of that reading path. -/

namespace PicoRV.Regs

open Silean
open Silean.Authoring

abbrev Word := Fin 32 → Bool
abbrev RegisterAddress := Fin 5 → Bool

module_ports ports where
  input resetn : .bit,
  input decoded_rs1 : .vector 5 .bit,
  input decoded_rs2 : .vector 5 .bit,
  input cpuregs_write : .bit,
  input latched_rd : .vector 5 .bit,
  input cpuregs_wrdata : .vector 32 .bit,
  output cpuregs_rs1 : .vector 32 .bit,
  output cpuregs_rs2 : .vector 32 .bit

abbrev wordType : SignalType := .vector 32 .bit
abbrev addressType : SignalType := .vector 5 .bit
def zeroAddressValue : addressType.Denote := fun _ => false
def zeroWordValue : wordType.Denote := fun _ => false

end PicoRV.Regs

namespace PicoRV

open Silean
open Silean.Authoring

module_design Regs (name := "picorv32_regs") where
  boundary (Regs.ports) (naming := Regs.Naming.ports)
  instances {
    zeroAddress (name := .indexed "constant" 0) :=
      Silean.Modules.Constant.design Regs.addressType Regs.zeroAddressValue,
    zeroWord (name := .indexed "constant" 1) :=
      Silean.Modules.Constant.design Regs.wordType Regs.zeroWordValue,
    rdZero (name := .indexed "equality" 0) :=
      Silean.Modules.Equality.design Regs.addressType,
    rdNonzero (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    requestedWrite (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    enabledWrite (name := .indexed "and" 1) := Silean.Primitives.andDesign,
    bank (name := .indexed "register_bank" 0) :=
      Silean.Modules.RegisterBank.design Regs.wordType 5 2,
    rs1Zero (name := .indexed "equality" 1) :=
      Silean.Modules.Equality.design Regs.addressType,
    rs1Mux (name := .indexed "mux" 0) :=
      Silean.Modules.Mux.design Regs.wordType,
    rs2Zero (name := .indexed "equality" 2) :=
      Silean.Modules.Equality.design Regs.addressType,
    rs2Mux (name := .indexed "mux" 1) :=
      Silean.Modules.Mux.design Regs.wordType }
  wiring {
    outputs {
      .cpuregs_rs1 := rs1Mux.result,
      .cpuregs_rs2 := rs2Mux.result }
    instance (.zeroAddress) {}
    instance (.zeroWord) {}
    instance (.rdZero) {
      .left := input.latched_rd,
      .right := zeroAddress.output }
    instance (.rdNonzero) { .input := rdZero.result }
    instance (.requestedWrite) {
      .left := input.resetn,
      .right := input.cpuregs_write }
    instance (.enabledWrite) {
      .left := requestedWrite.output,
      .right := rdNonzero.output }
    instance (.bank) {
      .readAddress 0 := input.decoded_rs1,
      .readAddress 1 := input.decoded_rs2,
      .writeEnable := enabledWrite.output,
      .writeAddress := input.latched_rd,
      .writeValue := input.cpuregs_wrdata }
    instance (.rs1Zero) {
      .left := input.decoded_rs1,
      .right := zeroAddress.output }
    instance (.rs1Mux) {
      .select := rs1Zero.result,
      .whenFalse := bank[.readValue 0],
      .whenTrue := zeroWord.output }
    instance (.rs2Zero) {
      .left := input.decoded_rs2,
      .right := zeroAddress.output }
    instance (.rs2Mux) {
      .select := rs2Zero.result,
      .whenFalse := bank[.readValue 1],
      .whenTrue := zeroWord.output }
  }

end PicoRV
