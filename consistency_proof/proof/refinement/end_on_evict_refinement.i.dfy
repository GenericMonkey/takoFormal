include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"
include "refinement_defns.i.dfy"
include "startendcb_common_proofs.i.dfy"

module EndOnEvictRefinementProof {
  import opened Types
  import opened TakoRefinementDefns
  import opened RefinementTypes
  import opened Execution
  import opened StartEndCBCommonProofs

  lemma EndOnEvictRefinement(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', EndOnEvict)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), EndOnEvict)
  {
    EndOnEvictValidRefinementStep(c, v, v');
    StartEndCBPreservesInv(c, v, v', EndOnEvict);
  }

  lemma EndOnEvictValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', EndOnEvict)
    requires RunningCallbackValuesAgree(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), EndOnEvict)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var step :| Tako.NextStep(c, v, v', step, EndOnEvict);
    assert step.TileStep?;
    assert step.tile_step.EngineStep?;
    assert step.tile_step.eng_step.FinishCallbackStep?;
    var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
    var entry' := v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
    assert EngReqToCBType(entry.cb_type).OnEvict?;
    var id: ThreadId := CallbackId(entry.addr, OnEvict, v.g.callback_epochs[entry.addr].epoch);
    var cb := Ee(entry.addr, false, ThreadInfo(id, End()));
    var spec_step := TakoSpec.EndOnEvictCBStep(cb);
    EvictIsValidEndOnEvictCBStep(c, v, v', step);
    assert TakoSpec.EndOnEvictCB(c_abs, v_abs, v_abs', cb);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, EndOnEvict);
  }

  lemma EvictIsValidEndOnEvictCBStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, EndOnEvict)
    requires RunningCallbackValuesAgree(c, v)
    ensures TakoSpec.EndOnEvictCB(
      ConstantsAbstraction(c), 
      VariablesAbstraction(c, v), 
      VariablesAbstraction(c, v'), 
      Ee(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr, false, ThreadInfo(
        CallbackId(
          v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr, 
          OnEvict, 
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
    assert EngReqToCBType(entry.cb_type).OnEvict?;
    var id: ThreadId := CallbackId(entry.addr, OnEvict, v.g.callback_epochs[entry.addr].epoch);
    var cb := Ee(entry.addr, false, ThreadInfo(id, End()));
    var spec_step := TakoSpec.EndOnEvictCBStep(cb);
    assert CallbackRunningInBufferLocation(c, v, entry.addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
    // trigger
  }
} 