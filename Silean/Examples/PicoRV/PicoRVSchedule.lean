import Silean.Examples.PicoRV.PicoRV
import Silean.Contracts.Cycle.CycleLayerConstruction

namespace Silean.Examples.PicoRV.PicoRV

open Silean Silean.Contracts.Cycle.Certification

/-! The schedule witnesses below establish a topological order for the
blackbox contracts. They are proof inputs, not execution order stored in the
module structure. -/

private abbrev controlOutputs : Layer.RuleOccurrence body childContracts := ⟨.control, .outputs⟩
private abbrev decoderOutputs : Layer.RuleOccurrence body childContracts := ⟨.decoder, .outputs⟩
private abbrev datapathRegistered : Layer.RuleOccurrence body childContracts := ⟨.datapath, .registered⟩
private abbrev memoryRegistered : Layer.RuleOccurrence body childContracts := ⟨.mem, .registered⟩
private abbrev memoryRdataQ : Layer.RuleOccurrence body childContracts := ⟨.mem, .memRdataQ⟩
private abbrev regsRs1 : Layer.RuleOccurrence body childContracts := ⟨.cpuregs, .cpuregs_rs1⟩
private abbrev regsRs2 : Layer.RuleOccurrence body childContracts := ⟨.cpuregs, .cpuregs_rs2⟩
private abbrev datapathNextPc : Layer.RuleOccurrence body childContracts := ⟨.datapath, .nextPc⟩
private abbrev datapathComparison : Layer.RuleOccurrence body childContracts := ⟨.datapath, .comparison⟩
private abbrev datapathWriteback : Layer.RuleOccurrence body childContracts := ⟨.datapath, .writeback⟩
private abbrev memoryLaRead : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaRead⟩
private abbrev memoryLaWrite : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaWrite⟩
private abbrev memoryLaAddr : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaAddr⟩
private abbrev memoryLaWdata : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaWdata⟩
private abbrev memoryLaWstrb : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaWstrb⟩
private abbrev memoryDone : Layer.RuleOccurrence body childContracts := ⟨.mem, .memDone⟩
private abbrev memoryRdataWord : Layer.RuleOccurrence body childContracts := ⟨.mem, .memRdataWord⟩
private abbrev memoryRdataLatched : Layer.RuleOccurrence body childContracts := ⟨.mem, .memRdataLatched⟩

private theorem controlOutputAvailable {available : Layer.Availability body childContracts}
    (called : controlOutputs ∈ available) (output : Control.Output) :
    Layer.sourceAvailable (fun _ : Input => True) available
      (context.instanceOutput Instance.control output) := by
  apply Layer.sourceAvailable_of_instanceOutput called
  change output ∈ Control.outputMap.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact ListIndex.get_eq (Control.outputMap.labels.locate output) ▸ List.get_mem _ _

private theorem decoderOutputAvailable {available : Layer.Availability body childContracts}
    (called : decoderOutputs ∈ available) (output : Decoder.Output) :
    Layer.sourceAvailable (fun _ : Input => True) available
      (context.instanceOutput Instance.decoder output) := by
  apply Layer.sourceAvailable_of_instanceOutput called
  change output ∈ Decoder.outputMap.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact ListIndex.get_eq (Decoder.outputMap.labels.locate output) ▸ List.get_mem _ _

/-! Invoke every child output rule in dependency order. The polymorphic finish
condition lets the same generic witness establish complete rule coverage,
child-state readiness, or availability of a selected parent output. -/
private noncomputable def completeSchedule :
    Layer.Schedule body childContracts (fun _ => True) (Layer.CoversAllRules body childContracts) [] :=
  .call controlOutputs (by intro input h; simp [Layer.RuleOccurrence.reads, Control.outputRule, SignalSelection.labels] at h) (by decide)
  (.call decoderOutputs (by intro input h; simp [Layer.RuleOccurrence.reads, Decoder.outputRule, SignalSelection.labels] at h) (by decide)
  (.call datapathRegistered (by intro input h; simp [Layer.RuleOccurrence.reads, Datapath.registeredRule, SignalSelection.labels] at h) (by decide)
  (.call memoryRegistered (by intro input h; simp [Layer.RuleOccurrence.reads, Memory.registeredRule, SignalSelection.labels] at h) (by decide)
  (.call memoryRdataQ (by intro input h; simp [Layer.RuleOccurrence.reads, Memory.memRdataQRule, SignalSelection.labels] at h) (by decide)
  (.call regsRs1 (by
    intro input h
    have equal : input = .decoded_rs1 := by
      simpa [Layer.RuleOccurrence.reads, Regs.cpuregsRs1Rule, SignalMap.select,
        SignalSelection.labels] using h
    subst input
    exact decoderOutputAvailable (by decide) .decoded_rs1) (by decide)
  (.call regsRs2 (by
    intro input h
    have equal : input = .decoded_rs2 := by
      simpa [Layer.RuleOccurrence.reads, Regs.cpuregsRs2Rule, SignalMap.select,
        SignalSelection.labels] using h
    subst input
    exact decoderOutputAvailable (by decide) .decoded_rs2) (by decide)
  (.call datapathNextPc (by
    intro input h
    cases input <;> simp_all [Layer.RuleOccurrence.reads, Datapath.nextPcRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> (apply controlOutputAvailable <;> decide)) (by decide)
  (.call datapathComparison
    (by
      intro input h
      cases input <;> simp_all [Layer.RuleOccurrence.reads, Datapath.comparisonRule,
        SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
        <;> (apply decoderOutputAvailable <;> decide)) (by decide)
  (.call datapathWriteback
    (by
      intro input h
      cases input <;> simp_all [Layer.RuleOccurrence.reads, Datapath.writebackRule,
        SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
        <;> (apply controlOutputAvailable <;> decide)) (by decide)
  (.call memoryLaRead (by
    intro input h
    cases input <;> simp_all [Layer.RuleOccurrence.reads, Memory.memLaReadRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first | exact trivial | (apply controlOutputAvailable <;> decide)) (by decide)
  (.call memoryLaWrite (by
    intro input h
    cases input <;> simp_all [Layer.RuleOccurrence.reads, Memory.memLaWriteRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first | exact trivial | (apply controlOutputAvailable <;> decide)) (by decide)
  (.call memoryLaAddr (by
    intro input h
    cases input <;> simp_all [Layer.RuleOccurrence.reads, Memory.memLaAddrRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first
        | (apply controlOutputAvailable <;> decide)
        | apply Layer.sourceAvailable_of_instanceOutput (body := body) (childContracts := childContracts)
            (child := Instance.datapath)
            (rule := Datapath.Rule.nextPc) (output := Datapath.Output.next_pc)
          · decide
          · simp [Layer.RuleOccurrence.writes, Datapath.nextPcRule,
              SignalMap.select, SignalSelection.labels]
        | apply Layer.sourceAvailable_of_instanceOutput (body := body) (childContracts := childContracts)
            (child := Instance.datapath)
            (rule := Datapath.Rule.registered) (output := Datapath.Output.reg_op1)
          · decide
          · simp [Layer.RuleOccurrence.writes, Datapath.registeredRule,
              SignalMap.select, SignalSelection.prepend, SignalSelection.labels]) (by decide)
  (.call memoryLaWdata (by
    intro input h
    cases input <;> simp_all [Layer.RuleOccurrence.reads, Memory.memLaWdataRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first
        | (apply controlOutputAvailable <;> decide)
        | apply Layer.sourceAvailable_of_instanceOutput (body := body) (childContracts := childContracts)
            (child := Instance.datapath)
            (rule := Datapath.Rule.registered) (output := Datapath.Output.reg_op2)
          · decide
          · simp [Layer.RuleOccurrence.writes, Datapath.registeredRule,
              SignalMap.select, SignalSelection.prepend, SignalSelection.labels]) (by decide)
  (.call memoryLaWstrb (by
    intro input h
    cases input <;> simp_all [Layer.RuleOccurrence.reads, Memory.memLaWstrbRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first
        | (apply controlOutputAvailable <;> decide)
        | apply Layer.sourceAvailable_of_instanceOutput (body := body) (childContracts := childContracts)
            (child := Instance.datapath)
            (rule := Datapath.Rule.registered) (output := Datapath.Output.reg_op1)
          · decide
          · simp [Layer.RuleOccurrence.writes, Datapath.registeredRule,
              SignalMap.select, SignalSelection.prepend, SignalSelection.labels]) (by decide)
  (.call memoryDone (by
    intro input h
    cases input <;> simp_all [Layer.RuleOccurrence.reads, Memory.memDoneRule,
      SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
      <;> first | exact trivial | (apply controlOutputAvailable <;> decide)) (by decide)
  (.call memoryRdataWord
    (by
      intro input h
      cases input <;> simp_all [Layer.RuleOccurrence.reads, Memory.memRdataWordRule,
        SignalMap.select, SignalSelection.prepend, SignalSelection.labels]
        <;> first
          | exact trivial
          | (apply controlOutputAvailable <;> decide)
          | apply Layer.sourceAvailable_of_instanceOutput (body := body) (childContracts := childContracts)
              (child := Instance.datapath)
              (rule := Datapath.Rule.registered) (output := Datapath.Output.reg_op1)
            · decide
            · simp [Layer.RuleOccurrence.writes, Datapath.registeredRule,
                SignalMap.select, SignalSelection.prepend, SignalSelection.labels]) (by decide)
  (.call memoryRdataLatched
    (by
      intro input h
      cases input <;> simp_all [Layer.RuleOccurrence.reads, Memory.memRdataLatchedRule,
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
    Layer.Schedule body childContracts (fun _ => True) (Layer.CoversAllRules body childContracts) [] :=
  completeSchedule

noncomputable def stateSchedule : Layer.StateSchedule body childContracts :=
  completeSchedule.mapFinish fun _available covers child input _ =>
    Layer.sourceAvailable_of_covers covers (body.wiring.instanceInput child input)

abbrev ParentOutputSchedule (output : Output) :=
  Layer.Schedule body childContracts (fun _ => True)
    (fun available => Layer.sourceAvailable (fun _ => True) available
      (body.wiring.moduleOutput output)) []

noncomputable def outputSchedule (output : Output) : ParentOutputSchedule output :=
  completeSchedule.mapFinish fun _available covers =>
    Layer.sourceAvailable_of_covers covers (body.wiring.moduleOutput output)

theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution := by
  unfold moduleStructure
  exact allRulesSchedule.hasAtMostOneSolution children
    (fun _ => trivial) allRulesSchedule.finished

end Silean.Examples.PicoRV.PicoRV
