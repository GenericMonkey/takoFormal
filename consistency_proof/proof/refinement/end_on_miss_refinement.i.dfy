include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"
include "refinement_defns.i.dfy"
include "startendcb_common_proofs.i.dfy"

module EndOnMissRefinementProof {
  import opened Types
  import opened Execution
  import opened TakoRefinementDefns
  import opened RefinementTypes
  import opened StartEndCBCommonProofs

  lemma EndOnMissRefinement(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', EndOnMiss)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), EndOnMiss)
  {
    EndOnMissValidRefinementStep(c, v, v');
    StartEndCBPreservesInv(c, v, v', EndOnMiss);
  }

  lemma EndOnMissValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', EndOnMiss)
    requires RunningCallbackValuesAgree(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), EndOnMiss)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var step :| Tako.NextStep(c, v, v', step, EndOnMiss);
    assert step.TileStep?;
    assert step.tile_step.EngineStep?;
    assert step.tile_step.eng_step.FinishCallbackStep?;
    var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
    var entry' := v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
    assert EngReqToCBType(entry.cb_type).OnMiss?;
    var id: ThreadId := CallbackId(entry.addr, OnMiss, v.g.callback_epochs[entry.addr].epoch);
    var cb := Me(entry.addr, Transform(entry.values), ThreadInfo(id, End()));
    var spec_step := TakoSpec.EndOnMissCBStep(cb);
    MissIsValidEndOnMissCBStep(c, v, v', step);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, EndOnMiss);
  }

  lemma MissIsValidEndOnMissCBStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, EndOnMiss)
    requires RunningCallbackValuesAgree(c, v)
    ensures TakoSpec.EndOnMissCB(
      ConstantsAbstraction(c), 
      VariablesAbstraction(c, v), 
      VariablesAbstraction(c, v'), 
      Me(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr,
      Transform(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].values),
      ThreadInfo(
        CallbackId(
          v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr, 
          OnMiss, 
          v.g.callback_epochs[v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr].epoch
        ), 
        End()
      ))
    )
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    assert step.TileStep?;
    assert step.tile_step.EngineStep?;
    assert step.tile_step.eng_step.FinishCallbackStep?;
    var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
    var entry' := v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
    assert EngReqToCBType(entry.cb_type).OnMiss?;
    var id: ThreadId := CallbackId(entry.addr, OnMiss, v.g.callback_epochs[entry.addr].epoch);
    var cb := Me(entry.addr, Transform(entry.values), ThreadInfo(id, End()));
    var spec_step := TakoSpec.EndOnMissCBStep(cb);
    assert CallbackRunningInBufferLocation(c, v, entry.addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
    // trigger
  }
} 