include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"
include "refinement_defns.i.dfy"
include "perfinst_common_proofs.i.dfy"

module PerformBranchRefinementProof {
  import opened Types
  import opened TakoRefinementDefns
  import opened RefinementTypes
  import opened Execution
  import opened PerformNextInstCommonProofs

  lemma PerformBranchRefinement(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', PerformBranch)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformBranch)
  {
    PerformBranchValidRefinementStep(c, v, v');
    PerformNextInstPreservesInv(c, v, v', PerformBranch);
  }

  
  lemma PerformBranchValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', PerformBranch)
    requires Inv(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformBranch)
  {
    var step :| Tako.NextStep(c, v, v', step, PerformBranch);
    assert step.TileStep?;
    if step.tile_step.CoreStep? {
      CorePerformBranchValidRefinementStep(c, v, v', step);
    } else {
      EnginePerformBranchValidRefinementStep(c, v, v', step);
    }
  }

  lemma EnginePerformBranchValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformBranch)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires InvPerfStore(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformBranch)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.Branch?;
    assert SpecCallbackId(c, v, id); // trigger
    assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx); // trigger
    var spec_step := TakoSpec.PerformBranchStep(id);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformBranch);
  }

  
  lemma CorePerformBranchValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformBranch)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires InvPerfStore(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformBranch)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.Branch?;
    assert ValidSpecCoreId(c, v, id);
    var spec_step := TakoSpec.PerformBranchStep(id);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformBranch);
  }
} 