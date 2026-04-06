include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"
include "refinement_defns.i.dfy"
include "perfinst_common_proofs.i.dfy"

module PerformFlushRefinementProof {
  import opened TakoRefinementDefns
  import opened RefinementTypes
  import opened Execution
  import opened PerformNextInstCommonProofs

  lemma PerformFlushRefinement(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', PerformFlush)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformFlush)
  {
    PerformFlushValidRefinementStep(c, v, v');
    PerformNextInstPreservesInv(c, v, v', PerformFlush);
  }

  lemma PerformFlushValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', PerformFlush)
    requires Inv(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformFlush)
  {
    var step :| Tako.NextStep(c, v, v', step, PerformFlush);
    assert step.TileStep?;
    assert step.tile_step.CoreStep?;
    CorePerformFlushValidRefinementStep(c, v, v', step);
  }

  lemma CorePerformFlushValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformFlush)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires InvPerfStore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformFlush)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.Flush?;
    var inst := step.tile_step.core_step.inst;
    var e := F(inst.addr, ThreadInfo(id, pc));
    assert ValidSpecCoreId(c, v, id);
    var spec_step := TakoSpec.PerformFlushStep(e);
    assert inst.addr.Morph? && inst.addr in v_abs.epochs by {
      reveal Program.Program.WF;
    }
    CorePerformFlushMeansOutEpoch(c, v, v', step);
    assert TakoSpec.PerformFlush(c_abs, v_abs, v_abs', e);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformFlush);
  }

  lemma CorePerformFlushMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformFlush)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.inst.addr.Morph?
    requires step.tile_step.core_step.inst.addr in VariablesAbstraction(c, v).epochs
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures VariablesAbstraction(c, v).epochs[step.tile_step.core_step.inst.addr].Out?
  {
    var addr := step.tile_step.core_step.inst.addr;
    forall val
      ensures !OnEvictInProgress(c, v, addr, val)
      ensures !OnWritebackInProgress(c, v, addr, val)
    {
      reveal InFlightOnEvictRequest;
      reveal InFlightOnWritebackRequest;
      reveal CallbackPresent;
    }
  }
} 