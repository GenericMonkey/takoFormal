include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"
include "refinement_defns.i.dfy"
include "startendcb_common_proofs.i.dfy"

module StartOnMissRefinementProof {
  import opened Types
  import opened TakoRefinementDefns
  import opened RefinementTypes
  import opened Execution
  import opened StartEndCBCommonProofs

  lemma StartOnMissRefinement(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', StartOnMiss)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), StartOnMiss)
  {
    StartOnMissValidRefinementStep(c, v, v');
    StartEndCBPreservesInv(c, v, v', StartOnMiss);
  }

  lemma StartOnMissValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', StartOnMiss)
    requires InvStartCallback(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), StartOnMiss)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var step :| Tako.NextStep(c, v, v', step, StartOnMiss);
    assert step.TileStep?;
    assert step.tile_step.EngineStep?;
    assert step.tile_step.eng_step.StartCallbackStep?;
    var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
    var entry' := v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
    assert EngReqToCBType(entry.cb_type).OnMiss?;
    var id: ThreadId := CallbackId(entry.addr, OnMiss, v.g.callback_epochs[entry.addr].epoch);
    var cb := Ms(entry.addr, ThreadInfo(id, Start()));
    var spec_step := TakoSpec.StartOnMissCBStep(cb);
    assert CBOrderTrackerValidIndex(c, v, entry.addr, step.tile_idx, 0);
    assert IsUnstartedBufferEntry(c, v, step.tile_idx, step.tile_step.eng_step.idx); // trigger
    assert CallbackPresentInBufferLocation(c, v, entry.addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
    assert TakoSpec.StartOnMissCB(c_abs, v_abs, v_abs', cb);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, StartOnMiss);
  }
} 