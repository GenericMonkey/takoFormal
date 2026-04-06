include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"
include "refinement_defns.i.dfy"
include "perfinst_common_proofs.i.dfy"

module PerformStoreRefinementProof {
  import opened Types
  import opened TakoRefinementDefns
  import opened RefinementTypes
  import opened Execution
  import opened PerformNextInstCommonProofs

  lemma PerformStoreRefinement(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', PerformStore)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformStore)
  {
    PerformStoreValidRefinementStep(c, v, v');
    PerformNextInstPreservesInv(c, v, v', PerformStore);
  }
  
  lemma PerformStoreValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', PerformStore)
    requires Inv(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformStore)
  {
    var step :| Tako.NextStep(c, v, v', step, PerformStore);
    assert step.TileStep?;
    if step.tile_step.CoreStep? {
      CorePerformStoreValidRefinementStep(c, v, v', step);
    } else {
      EnginePerformStoreValidRefinementStep(c, v, v', step);
    }
  }

  lemma EnginePerformStoreRegularAddressValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformStore)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.inst.addr.Regular?
    requires InvPerfStore(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformStore)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.Store?;
    var inst := step.tile_step.eng_step.inst;
    var wval_real := if inst.val.Reg? then v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].regs[inst.val.reg] else Just(inst.val.val);
    var e := W(inst.addr, wval_real, ThreadInfo(id, pc));
    var spec_step := TakoSpec.PerformRegularStoreStep(e);
    assert SpecCallbackId(c, v, id); // trigger
    assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx); // trigger
    assert TakoSpec.UpdatePCOnly(c_abs, v_abs, v_abs', e);
    assert TakoSpec.PerformRegularStore(c_abs, v_abs, v_abs', e);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformStore);
  }

  lemma EnginePerformStoreMorphAddressValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformStore)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.inst.addr.Morph?
    requires InvPerfStore(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformStore)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.Store?;
    var inst := step.tile_step.eng_step.inst;
    var wval_real := if inst.val.Reg? then v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].regs[inst.val.reg] else Just(inst.val.val);
    var e := Wcb(inst.addr, wval_real, ThreadInfo(id, pc));
    var spec_step := TakoSpec.PerformMorphStoreStep(e);
    assert SpecCallbackId(c, v, id);
    assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx); // trigger
    assert ValuesMatchForCallbackId(c, v, v_abs.pcs[id], step.tile_idx, step.tile_step.eng_step.idx);
    assert TakoSpec.UpdatePCOnly(c_abs, v_abs, v_abs', e);
    assert TakoSpec.UpdateCboCommon(c_abs, v_abs, v_abs', e);
    assert TakoSpec.PerformMorphStore(c_abs, v_abs, v_abs', e);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformStore);
  }

  lemma EnginePerformStoreValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformStore)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires InvPerfStore(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformStore)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.Store?;
    var inst := step.tile_step.eng_step.inst;
    if inst.addr.Regular? {
      EnginePerformStoreRegularAddressValidRefinementStep(c, v, v', step);
    } else {
      EnginePerformStoreMorphAddressValidRefinementStep(c, v, v', step);
    }
  }

  lemma CorePerformStoreRegularAddressValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformStore)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.inst.addr.Regular?
    requires InvPerfStore(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformStore)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.Store?;
    var inst := step.tile_step.core_step.inst;
    var wval_real := if inst.val.Reg? then v.tiles[step.tile_idx].core.regs[inst.val.reg] else Just(inst.val.val);
    var e := W(inst.addr, wval_real, ThreadInfo(id, pc));
    var spec_step := TakoSpec.PerformRegularStoreStep(e);
    assert ValidSpecCoreId(c, v, id);
    assert TakoSpec.UpdatePCOnly(c_abs, v_abs, v_abs', e);
    assert TakoSpec.PerformRegularStore(c_abs, v_abs, v_abs', e);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformStore);
  }

  lemma CorePerformStoreMorphAddressValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformStore)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.inst.addr.Morph?
    requires InvPerfStore(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformStore)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.Store?;
    var inst := step.tile_step.core_step.inst;
    var wval_real := if inst.val.Reg? then v.tiles[step.tile_idx].core.regs[inst.val.reg] else Just(inst.val.val);
    var e := Wcb(inst.addr, wval_real, ThreadInfo(id, pc));
    var spec_step := TakoSpec.PerformMorphStoreStep(e);
    assert ValidSpecCoreId(c, v, id);
    assert TakoSpec.UpdatePCOnly(c_abs, v_abs, v_abs', e);
    assert TakoSpec.PerformMorphStore(c_abs, v_abs, v_abs', e);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformStore);
  }

  lemma CorePerformStoreValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformStore)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires InvPerfStore(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformStore)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.Store?;
    var inst := step.tile_step.core_step.inst;
    if inst.addr.Regular? {
      CorePerformStoreRegularAddressValidRefinementStep(c, v, v', step);
    } else {
      CorePerformStoreMorphAddressValidRefinementStep(c, v, v', step);
    }
  }
}