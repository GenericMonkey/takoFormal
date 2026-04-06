include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"
include "refinement_defns.i.dfy"
include "perfinst_common_proofs.i.dfy"

module PerformRMWRefinementProof {
  import opened Types
  import opened TakoRefinementDefns
  import opened RefinementTypes
  import opened Execution
  import opened PerformNextInstCommonProofs

  lemma PerformRMWRefinement(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', PerformRMW)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformRMW)
  {
    PerformRMWValidRefinementStep(c, v, v');
    PerformNextInstPreservesInv(c, v, v', PerformRMW);
  }

  lemma PerformRMWValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', PerformRMW)
    requires Inv(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformRMW)
  {
    var step :| Tako.NextStep(c, v, v', step, PerformRMW);
    assert step.TileStep?;
    if step.tile_step.CoreStep? {
      CorePerformRMWValidRefinementStep(c, v, v', step);
    } else {
      EnginePerformRMWValidRefinementStep(c, v, v', step);
    }
  }

  lemma EnginePerformRMWValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires InvPerfStore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires EngineLoadableMatchesLastWriteMorph(c, v)
    requires AddrInEpochMeansEventsWellformed(c, v)
    requires AddrInEpochMeansEventsMatchAddrAtomicity(c, v)
    requires WritesToAddrWellFormed(c, v)
    requires EngineLoadableMatchesLastWriteRegular(c, v)
    requires AllWritesInWritesToAddr(c, v)
    requires MoDeterminedByWritesToAddrOrder(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformRMW)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.RMW?;
    var inst := step.tile_step.eng_step.inst;
    if inst.addr.Regular? {
      EnginePerformRMWRegularAddressValidRefinementStep(c, v, v', step);
    } else {
      EnginePerformRMWMorphAddressValidRefinementStep(c, v, v', step);
    }
  }

  
  lemma CorePerformRMWValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires Inv(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformRMW)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.RMW?;
    var inst := step.tile_step.core_step.inst;
    if inst.addr.Regular? {
      CorePerformRMWRegularAddressValidRefinementStep(c, v, v', step);
    } else {
      CorePerformRMWMorphAddressValidRefinementStep(c, v, v', step);
    }
  }

  lemma EnginePerformRMWMorphAddressValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.inst.addr.Morph?
    requires InvPerfStore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    // new invs
    requires EngineLoadableMatchesLastWriteMorph(c, v)
    requires AddrInEpochMeansEventsWellformed(c, v)
    requires AddrInEpochMeansEventsMatchAddrAtomicity(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformRMW)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.RMW?;
    var inst := step.tile_step.eng_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].regs[inst.wval.reg] else Just(inst.wval.val);
    var e := RMWcb(inst.addr, v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.val, wval_real, ThreadInfo(id, pc));
    var spec_step := TakoSpec.PerformMorphRMWStep(e, inst.reg);
    assert SpecCallbackId(c, v, id); // trigger
    assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx); // trigger
    EnginePerformRMWMorphAddressIsInEpoch(c, v, v', step);
    EnginePerformRMWMorphAddressValueIsWriteOrMissEnd(c, v, v', step);
    assert TakoSpec.UpdateCboCommon(c_abs, v_abs, v_abs', e);
    assert TakoSpec.PerformMorphRMW(c_abs, v_abs, v_abs', e, inst.reg);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformRMW);
  }

  lemma EnginePerformRMWMorphAddressIsInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.inst.addr.Morph?
    requires InvPerfStore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures step.tile_step.eng_step.inst.addr in VariablesAbstraction(c, v).epochs
    ensures VariablesAbstraction(c, v).epochs[step.tile_step.eng_step.inst.addr].In?
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.RMW?;
    var inst := step.tile_step.eng_step.inst;
    assert SpecCallbackId(c, v, id); // trigger
    assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx); // trigger
    assert inst.addr in v_abs.epochs;
    assert v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.Loadable();
    assert !L2AddrNotInCache(c, v, step.tile_idx, inst.addr);
    var l2_idx: nat :| NonEmptyNonPendingL2CacheEntry(c, v, step.tile_idx, l2_idx)
      && v.tiles[step.tile_idx].l2.cache[l2_idx].addr == inst.addr;
    assert !DirIL2CacheEntry(c, v, step.tile_idx, l2_idx);
    if PrivateMorph(inst.addr) {
      reveal MorphAddrIsInL2CacheEntry;
      assert v_abs.epochs[inst.addr].In?;
    } else {
      assert SharedMorph(inst.addr);
      assert !L3AddrNotInCache(c, v, c.addr_map(inst.addr), inst.addr);
      reveal MorphAddrIsInL3CacheEntry;
      assert v_abs.epochs[inst.addr].In?;
    }
  }

  lemma EnginePerformRMWMorphAddressValueIsWriteOrMissEnd(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.inst.addr.Morph?
    requires InvPerfStore(c, v)
    requires EngineLoadableMatchesLastWriteMorph(c, v)
    requires AddrInEpochMeansEventsWellformed(c, v)
    requires AddrInEpochMeansEventsMatchAddrAtomicity(c, v)

    requires step.tile_step.eng_step.inst.addr in VariablesAbstraction(c, v).epochs
    requires VariablesAbstraction(c, v).epochs[step.tile_step.eng_step.inst.addr].In?
    ensures (
      && var val := if VariablesAbstraction(c, v).epochs[step.tile_step.eng_step.inst.addr].wcb.Some? then 
        VariablesAbstraction(c, v).epochs[step.tile_step.eng_step.inst.addr].wcb.val 
      else 
        VariablesAbstraction(c, v).epochs[step.tile_step.eng_step.inst.addr].me;
      && (val.RMWcb? || val.Me?)
      && (if val.RMWcb? then val.wval else val.val) == v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.val
    )
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.RMW?;
    var inst := step.tile_step.eng_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].regs[inst.wval.reg] else Just(inst.wval.val);
    var e := RMWcb(inst.addr, v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.val, wval_real, ThreadInfo(id, pc));
    var spec_step := TakoSpec.PerformMorphRMWStep(e, inst.reg);
    var val := if v_abs.epochs[inst.addr].wcb.Some? then v_abs.epochs[inst.addr].wcb.val else v_abs.epochs[inst.addr].me;
    assert val.RMWcb? || val.Me? by {
      assert inst.addr.atomic by {
        reveal Program.Program.WF;
      }
      assert val.CBWrite() || val.Me?;
      assert val.addr == inst.addr;
    }
    assert (if val.RMWcb? then val.wval else val.val) == e.rval;
  }

  lemma CorePerformRMWMorphAddressValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.inst.addr.Morph?
    requires InvPerfStore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    // new invs
    requires CoreLoadableMatchesLastWriteMorph(c, v)
    requires AddrInEpochMeansEventsWellformed(c, v)
    requires AddrInEpochMeansEventsMatchAddrAtomicity(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformRMW)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.RMW?;
    var inst := step.tile_step.core_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].core.regs[inst.wval.reg] else Just(inst.wval.val);
    var e := RMWcb(inst.addr, v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.val, wval_real, ThreadInfo(id, pc));
    var spec_step := TakoSpec.PerformMorphRMWStep(e, inst.reg);
    assert ValidSpecCoreId(c, v, id);
    CorePerformRMWMorphAddressIsInEpoch(c, v, v', step);
    CorePerformRMWMorphAddressValueIsWriteOrMissEnd(c, v, v', step);
    var val_e := if v_abs.epochs[inst.addr].wcb.Some? then v_abs.epochs[inst.addr].wcb.val else v_abs.epochs[inst.addr].me;
    var val := if val_e.RMWcb? then val_e.wval else val_e.val;
    assert ThreadIdMatchesCoreId(c, v, id);
    assert v_abs'.pcs[e.info.id].pc == v_abs.pcs[e.info.id].pc.(pc := e.info.pc.pc + 1);
    assert v_abs'.pcs[e.info.id].regs == v_abs.pcs[e.info.id].regs[ inst.reg := val ];
    assert v_abs'.pcs[e.info.id].vals == v_abs.pcs[e.info.id].vals + [ val ];
    assert TakoSpec.UpdatePCWithVal(c_abs, v_abs, v_abs', e, inst.reg);
    assert TakoSpec.PerformMorphRMW(c_abs, v_abs, v_abs', e, inst.reg);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformRMW);
  }

  lemma CorePerformRMWMorphAddressIsInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.inst.addr.Morph?
    requires InvPerfStore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures step.tile_step.core_step.inst.addr in VariablesAbstraction(c, v).epochs
    ensures VariablesAbstraction(c, v).epochs[step.tile_step.core_step.inst.addr].In?
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.RMW?;
    var inst := step.tile_step.core_step.inst;
    assert ValidSpecCoreId(c, v, id); // trigger
    assert inst.addr in v_abs.epochs;
    assert v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.Loadable();
    assert !L2AddrNotInCache(c, v, step.tile_idx, inst.addr);
    var l2_idx: nat :| NonEmptyNonPendingL2CacheEntry(c, v, step.tile_idx, l2_idx)
      && v.tiles[step.tile_idx].l2.cache[l2_idx].addr == inst.addr;
    assert !DirIL2CacheEntry(c, v, step.tile_idx, l2_idx);
    if PrivateMorph(inst.addr) {
      reveal MorphAddrIsInL2CacheEntry;
      assert v_abs.epochs[inst.addr].In?;
    } else {
      assert SharedMorph(inst.addr);
      assert !L3AddrNotInCache(c, v, c.addr_map(inst.addr), inst.addr);
      reveal MorphAddrIsInL3CacheEntry;
      assert v_abs.epochs[inst.addr].In?;
    }
  }

  lemma CorePerformRMWMorphAddressValueIsWriteOrMissEnd(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.inst.addr.Morph?
    requires InvPerfStore(c, v)
    requires CoreLoadableMatchesLastWriteMorph(c, v)
    requires AddrInEpochMeansEventsWellformed(c, v)
    requires AddrInEpochMeansEventsMatchAddrAtomicity(c, v)

    requires step.tile_step.core_step.inst.addr in VariablesAbstraction(c, v).epochs
    requires VariablesAbstraction(c, v).epochs[step.tile_step.core_step.inst.addr].In?
    ensures (
      && var val := if VariablesAbstraction(c, v).epochs[step.tile_step.core_step.inst.addr].wcb.Some? then 
        VariablesAbstraction(c, v).epochs[step.tile_step.core_step.inst.addr].wcb.val 
      else 
        VariablesAbstraction(c, v).epochs[step.tile_step.core_step.inst.addr].me;
      && (val.RMWcb? || val.Me?)
      && (if val.RMWcb? then val.wval else val.val) == v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.val
    )
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.RMW?;
    var inst := step.tile_step.core_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].core.regs[inst.wval.reg] else Just(inst.wval.val);
    var e := RMWcb(inst.addr, v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.val, wval_real, ThreadInfo(id, pc));
    var spec_step := TakoSpec.PerformMorphRMWStep(e, inst.reg);
    var val := if v_abs.epochs[inst.addr].wcb.Some? then v_abs.epochs[inst.addr].wcb.val else v_abs.epochs[inst.addr].me;
    assert val.RMWcb? || val.Me? by {
      assert inst.addr.atomic by {
        reveal Program.Program.WF;
      }
      assert val.CBWrite() || val.Me?;
      assert val.addr == inst.addr;
    }
    assert (if val.RMWcb? then val.wval else val.val) == e.rval;
  }

  lemma EnginePerformRMWRegularAddressValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.inst.addr.Regular?
    requires InvPerfStore(c, v)
    requires WritesToAddrWellFormed(c, v)
    requires EngineLoadableMatchesLastWriteRegular(c, v)
    requires AllWritesInWritesToAddr(c, v)
    requires MoDeterminedByWritesToAddrOrder(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformRMW)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.RMW?;
    var inst := step.tile_step.eng_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].regs[inst.wval.reg] else Just(inst.wval.val);
    var r := RMW(inst.addr, v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.val, wval_real, ThreadInfo(id, pc));
    var w := v.g.writes_to_addr[inst.addr][|v.g.writes_to_addr[inst.addr]| -1];
    var spec_step := TakoSpec.PerformRegularRMWStep(r, w, inst.reg);
    assert SpecCallbackId(c, v, id); // trigger
    assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx); // trigger
    EnginePerformRMWRegularAddressValueIsLastWrite(c, v, v', step);
    EnginePerformRMWRegularAddressWritesToAddrLastIsMoLast(c, v, v', step);
    assert TakoSpec.PerformRegularRMW(c_abs, v_abs, v_abs', r, w, inst.reg);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformRMW);
  }

  lemma EnginePerformRMWRegularAddressValueIsLastWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.inst.addr.Regular?
    requires InvPerfStore(c, v)
    requires WritesToAddrWellFormed(c, v)
    requires EngineLoadableMatchesLastWriteRegular(c, v)
    ensures (
      && var w := v.g.writes_to_addr[step.tile_step.eng_step.inst.addr][|v.g.writes_to_addr[step.tile_step.eng_step.inst.addr]| -1];
      && (w.RMW? || (w.W? && w.info.id.Initial?))
      && w in VariablesAbstraction(c, v).execution.WritesToAddr(step.tile_step.eng_step.inst.addr)
      && (if w.RMW? then w.wval else w.val) == v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.val
    )
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.RMW?;
    var inst := step.tile_step.eng_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].regs[inst.wval.reg] else Just(inst.wval.val);
    var r := RMW(inst.addr, v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.val, wval_real, ThreadInfo(id, pc));
    var w := v.g.writes_to_addr[inst.addr][|v.g.writes_to_addr[inst.addr]| -1];
    var spec_step := TakoSpec.PerformRegularRMWStep(r, w, inst.reg);
    // assert SpecCallbackId(c, v, id); // trigger
    // assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx); // trigger
    assert (w.RMW? || (w.W? && w.info.id.Initial?)) by {
      assert inst.addr.atomic by {
        assert c.program.AtomicInstructionsOnlyReferenceAtomicAddrs() by {
          reveal Program.Program.WF;
        }
        assert inst.RMW?;
        // if addr in c.program.onMissCBs {
        // } else if addr in c.program.onEvictCBs {
        // } else {
        //   assert addr in c.program.onWBCBs;
        // }
      }
      // assert !w.RMW?;
    }
    assert w in v_abs.execution.WritesToAddr(inst.addr) by {
      assert w in v_abs.execution.pre.events;
      assert w.addr == inst.addr;
      assert SameAddr(w.addr, inst.addr);
    }
    assert (if w.RMW? then w.wval else w.val) == r.rval;
  }

  lemma EnginePerformRMWRegularAddressWritesToAddrLastIsMoLast(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.inst.addr.Regular?
    requires AllWritesInWritesToAddr(c, v)
    requires MoDeterminedByWritesToAddrOrder(c, v)
    ensures forall w' : Event | w' in VariablesAbstraction(c, v).execution.WritesToAddr(step.tile_step.eng_step.inst.addr) 
      :: !((v.g.writes_to_addr[step.tile_step.eng_step.inst.addr][|v.g.writes_to_addr[step.tile_step.eng_step.inst.addr]| -1], w') in VariablesAbstraction(c, v).execution.wit.mo)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
    var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
    var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
    var pc: PC := PC(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].pc, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].count);
    assert step.tile_step.eng_step.NextInstStep?;
    assert step.tile_step.eng_step.inst.RMW?;
    var inst := step.tile_step.eng_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].regs[inst.wval.reg] else Just(inst.wval.val);
    var r := RMW(inst.addr, v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.val, wval_real, ThreadInfo(id, pc));
    var w := v.g.writes_to_addr[inst.addr][|v.g.writes_to_addr[inst.addr]| -1];
    var spec_step := TakoSpec.PerformRegularRMWStep(r, w, inst.reg);
    // mo iff w in writes_to_addr, w' in writes_to_addr, idx_w < idx_w'
    // prob: what about events in writes to addr that aren't in writes_to_addr? (there aren't any)
    forall w' : Event | w' in v_abs.execution.WritesToAddr(inst.addr) 
      ensures !((w, w') in v_abs.execution.wit.mo)
    {
      assert w' in v.g.writes_to_addr[inst.addr];
      var idx: nat :| idx < |v.g.writes_to_addr[inst.addr]| && w' == v.g.writes_to_addr[inst.addr][idx];
    }
  }

  lemma CorePerformRMWRegularAddressValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.inst.addr.Regular?
    requires InvPerfStore(c, v)
    requires WritesToAddrWellFormed(c, v)
    requires CoreLoadableMatchesLastWriteRegular(c, v)
    requires AllWritesInWritesToAddr(c, v)
    requires MoDeterminedByWritesToAddrOrder(c, v)
    ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), PerformRMW)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.RMW?;
    var inst := step.tile_step.core_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].core.regs[inst.wval.reg] else Just(inst.wval.val);
    var r := RMW(inst.addr, v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.val, wval_real, ThreadInfo(id, pc));
    var w := v.g.writes_to_addr[inst.addr][|v.g.writes_to_addr[inst.addr]| -1];
    var spec_step := TakoSpec.PerformRegularRMWStep(r, w, inst.reg);
    assert ValidSpecCoreId(c, v, id);
    CorePerformRMWRegularAddressValueIsLastWrite(c, v, v', step);
    CorePerformRMWRegularAddressWritesToAddrLastIsMoLast(c, v, v', step);
    assert v_abs'.pcs[r.info.id].pc == v_abs.pcs[r.info.id].pc.(pc := r.info.pc.pc + 1);
    assert v_abs'.pcs[r.info.id].regs == v_abs.pcs[r.info.id].regs[ inst.reg := r.rval ];
    assert v_abs'.pcs[r.info.id].vals == v_abs.pcs[r.info.id].vals + [ r.rval ];
    assert TakoSpec.UpdatePCWithVal(c_abs, v_abs, v_abs', r, inst.reg);
    assert TakoSpec.PerformRegularRMW(c_abs, v_abs, v_abs', r, w, inst.reg);
    assert TakoSpec.NextStep(c_abs, v_abs, v_abs', spec_step);
    assert TakoSpec.NextStepRefined(c_abs, v_abs, v_abs', spec_step, PerformRMW);
  }

  lemma CorePerformRMWRegularAddressValueIsLastWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.inst.addr.Regular?
    requires InvPerfStore(c, v)
    requires WritesToAddrWellFormed(c, v)
    requires CoreLoadableMatchesLastWriteRegular(c, v)
    ensures (
      && var w := v.g.writes_to_addr[step.tile_step.core_step.inst.addr][|v.g.writes_to_addr[step.tile_step.core_step.inst.addr]| -1];
      && (w.RMW? || (w.W? && w.info.id.Initial?))
      && w in VariablesAbstraction(c, v).execution.WritesToAddr(step.tile_step.core_step.inst.addr)
      && (if w.RMW? then w.wval else w.val) == v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.val
    )
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.RMW?;
    var inst := step.tile_step.core_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].core.regs[inst.wval.reg] else Just(inst.wval.val);
    var r := RMW(inst.addr, v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.val, wval_real, ThreadInfo(id, pc));
    var w := v.g.writes_to_addr[inst.addr][|v.g.writes_to_addr[inst.addr]| -1];
    var spec_step := TakoSpec.PerformRegularRMWStep(r, w, inst.reg);
    assert (w.RMW? || (w.W? && w.info.id.Initial?)) by {
      assert inst.addr.atomic by {
        assert c.program.AtomicInstructionsOnlyReferenceAtomicAddrs() by {
          reveal Program.Program.WF;
        }
        assert inst.RMW?;
        // if addr in c.program.onMissCBs {
        // } else if addr in c.program.onEvictCBs {
        // } else {
        //   assert addr in c.program.onWBCBs;
        // }
      }
    }
    assert w in v_abs.execution.WritesToAddr(inst.addr) by {
      assert w in v_abs.execution.pre.events;
      assert w.addr == inst.addr;
      assert SameAddr(w.addr, inst.addr);
    }
    assert (if w.RMW? then w.wval else w.val) == r.rval;
  }

  lemma CorePerformRMWRegularAddressWritesToAddrLastIsMoLast(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, PerformRMW)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.inst.addr.Regular?
    requires AllWritesInWritesToAddr(c, v)
    requires MoDeterminedByWritesToAddrOrder(c, v)
    ensures forall w' : Event | w' in VariablesAbstraction(c, v).execution.WritesToAddr(step.tile_step.core_step.inst.addr) 
      :: !((v.g.writes_to_addr[step.tile_step.core_step.inst.addr][|v.g.writes_to_addr[step.tile_step.core_step.inst.addr]| -1], w') in VariablesAbstraction(c, v).execution.wit.mo)
  {
    var c_abs := ConstantsAbstraction(c);
    var v_abs := VariablesAbstraction(c, v);
    var v_abs' := VariablesAbstraction(c, v');
    var id: ThreadId := CoreId(step.tile_idx);
    var pc: PC := PC(v.tiles[step.tile_idx].core.pc, v.tiles[step.tile_idx].core.count);
    assert step.tile_step.core_step.NextInstStep?;
    assert step.tile_step.core_step.inst.RMW?;
    var inst := step.tile_step.core_step.inst;
    var wval_real := if inst.wval.Reg? then v.tiles[step.tile_idx].core.regs[inst.wval.reg] else Just(inst.wval.val);
    var r := RMW(inst.addr, v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.val, wval_real, ThreadInfo(id, pc));
    var w := v.g.writes_to_addr[inst.addr][|v.g.writes_to_addr[inst.addr]| -1];
    var spec_step := TakoSpec.PerformRegularRMWStep(r, w, inst.reg);
    // mo iff w in writes_to_addr, w' in writes_to_addr, idx_w < idx_w'
    // prob: what about events in writes to addr that aren't in writes_to_addr? (there aren't any)
    forall w' : Event | w' in v_abs.execution.WritesToAddr(inst.addr) 
      ensures !((w, w') in v_abs.execution.wit.mo)
    {
      assert w' in v.g.writes_to_addr[inst.addr];
      var idx: nat :| idx < |v.g.writes_to_addr[inst.addr]| && w' == v.g.writes_to_addr[inst.addr][idx];
    }
  }
}