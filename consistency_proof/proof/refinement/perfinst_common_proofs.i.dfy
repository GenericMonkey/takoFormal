include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"
include "refinement_defns.i.dfy"
include "invproofs/network_diff_cbs.i.dfy"
include "invproofs/onmiss_private.i.dfy"
include "invproofs/onevict_private.i.dfy"
include "invproofs/onwb_private.i.dfy"
include "invproofs/onmiss_shared.i.dfy"
include "invproofs/onevict_shared.i.dfy"
include "invproofs/onwb_shared.i.dfy"
include "invproofs/engbound_unique.i.dfy"
include "invproofs/onmiss_onespot.i.dfy"
include "invproofs/onmiss_resp_evict.i.dfy"
include "invproofs/onmiss_resp_wb.i.dfy"
include "invproofs/cbheadmiss_evict.i.dfy"
include "invproofs/cbheadmiss_wb.i.dfy"
include "invproofs/engreqqueuemiss_evict.i.dfy"
include "invproofs/engreqqueuemiss_wb.i.dfy"
include "invproofs/cachebound_unique.i.dfy"
include "invproofs/cbordertracker_wf.i.dfy"
include "invproofs/engreq_properties.i.dfy"
include "invproofs/outepoch_defn.i.dfy"
include "invproofs/inepoch_defn.i.dfy"
include "invproofs/onevict_loadable.i.dfy"
include "invproofs/onwb_loadable.i.dfy"
include "invproofs/addr_in_cache.i.dfy"
include "invproofs/cborder_epoch.i.dfy"
include "invproofs/diri_loadable.i.dfy"
include "invproofs/dirtybit_epoch.i.dfy"
include "invproofs/dirtybit_properties.i.dfy"
include "invproofs/coh_msg_wf.i.dfy"
include "invproofs/evict_write.i.dfy"
include "invproofs/wb_write.i.dfy"
include "invproofs/write_to_addr_properties.i.dfy"


module PerformNextInstCommonProofs {
  import opened Types
  import opened TakoRefinementDefns
  import opened RefinementTypes
  import opened Execution
  import opened EngineTypes

  lemma PerformNextInstPreservesWF(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    ensures v'.WF(c)
  {}

  lemma PerformNextInstPreservesCoreRuntimeDataMatchesWithGhostRuntimeData(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvPerfStore(c, v)
    ensures CoreRuntimeDataMatchesWithGhostRuntimeData(c, v')
  {
    if step.tile_step.CoreStep? {
      var id: ThreadId := CoreId(step.tile_idx);
      assert ValidSpecCoreId(c, v', id);
      assert ThreadIdMatchesCoreId(c, v', id);
      forall id2: ThreadId | id2 != id && ValidSpecCoreId(c, v', id2)
        ensures ThreadIdMatchesCoreId(c, v', id2)
      {
        assert ValidSpecCoreId(c, v, id2); // trigger
      }
      assert CoreRuntimeDataMatchesWithGhostRuntimeData(c, v');
    } else {
      assert step.tile_step.EngineStep?;
      var addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
      var cb_type := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
      var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
      assert !ValidSpecCoreId(c, v', id);
      forall id2: ThreadId | ValidSpecCoreId(c, v', id2)
        ensures ThreadIdMatchesCoreId(c, v', id2)
      {
        assert ValidSpecCoreId(c, v, id2); // trigger
      }
      assert CoreRuntimeDataMatchesWithGhostRuntimeData(c, v');
    }
  }

  lemma CorePerformNextInstPreservesRunningCallbackValuesAgree(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.NextInstStep?
    requires InvPerfStore(c, v)
    ensures RunningCallbackValuesAgree(c, v')
  {
    forall addr, cb, tile: nat, buf | CallbackRunningInBufferLocation(c, v', addr, cb, tile, buf)
      ensures (
        && addr in v'.g.callback_epochs
        && var id: ThreadId := CallbackId(addr, cb, v'.g.callback_epochs[addr].epoch);
        && CurrentSpecCallbackId(c, v', id)
        && Engine.IsNextCallback(c.tiles[tile].engine, v.tiles[tile].engine, buf)
        && ValuesMatchForCallbackId(c, v', v'.g.pcs[id], tile, buf)
      )
    {
      assert CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf);
      assert addr in v.g.callback_epochs;
      var id: ThreadId := CallbackId(addr, cb, v.g.callback_epochs[addr].epoch);
      assert CurrentSpecCallbackId(c, v, id);
      assert ValuesMatchForCallbackId(c, v, v.g.pcs[id], tile, buf);
    }
  }

  lemma EnginePerformNextInstPreservesRunningCallbackValuesAgree(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.NextInstStep?
    requires InvPerfStore(c, v)
    ensures RunningCallbackValuesAgree(c, v')
  {
      forall addr, cb, tile: nat, buf: nat | CallbackRunningInBufferLocation(c, v', addr, cb, tile, buf)
        ensures (
          && addr in v'.g.callback_epochs
          && var id: ThreadId := CallbackId(addr, cb, v'.g.callback_epochs[addr].epoch);
          && CurrentSpecCallbackId(c, v', id)
          && Engine.IsNextCallback(c.tiles[tile].engine, v.tiles[tile].engine, buf)
          && ValuesMatchForCallbackId(c, v', v'.g.pcs[id], tile, buf)
        )
      {
        assert CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf);
        var id: ThreadId := CallbackId(addr, cb, v'.g.callback_epochs[addr].epoch);
        var cur_addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
        var cur_cb := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
        var cur_id: ThreadId := CallbackId(cur_addr, cur_cb, v.g.callback_epochs[addr].epoch);
        if tile == step.tile_idx && buf == step.tile_step.eng_step.idx {
          assert CurrentSpecCallbackId(c, v, id);
          assert CurrentSpecCallbackId(c, v, cur_id);
          assert ValuesMatchForCallbackId(c, v', v'.g.pcs[id], tile, buf);
        } else {
          assert SpecCallbackId(c, v, id);
          if id == cur_id {
            assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx);
            assert false;
          }
          assert ValuesMatchForCallbackId(c, v', v'.g.pcs[id], tile, buf);
        }
      }
  }

  lemma PerformNextInstPreservesRunningCallbackValuesAgree(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvPerfStore(c, v)
    ensures RunningCallbackValuesAgree(c, v')
  {
    if step.tile_step.CoreStep? {
      CorePerformNextInstPreservesRunningCallbackValuesAgree(c, v, v', step, re);
    } else {
      assert step.tile_step.EngineStep?;
      EnginePerformNextInstPreservesRunningCallbackValuesAgree(c, v, v', step, re);
    }
  }

  lemma PerformNextInstPreservesUniqueTileForCallbackAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvPerfStore(c, v)
    ensures UniqueTileForCallbackAddr(c, v')
  {
    if step.tile_step.CoreStep? {
      forall addr: Address, cb1: CallbackType, cb2: CallbackType, t1: nat, t2: nat, b1: nat, b2: nat | (
        && CallbackPresentInBufferLocation(c, v', addr, cb1, t1, b1) 
        && CallbackPresentInBufferLocation(c, v', addr, cb2, t2, b2)
      ) 
        ensures t1 == t2
        ensures ((cb1 == cb2) ==> b1 == b2)
        ensures !(cb1.OnEvict? && cb2.OnWriteBack?)
      {
        assert CallbackPresentInBufferLocation(c, v, addr, cb1, t1, b1);
        assert CallbackPresentInBufferLocation(c, v, addr, cb2, t2, b2);
      }
      assert UniqueTileForCallbackAddr(c, v');
    } else {
      assert step.tile_step.EngineStep?;
      forall addr: Address, cb1: CallbackType, cb2: CallbackType, t1: nat, t2: nat, b1: nat, b2: nat | (
        && CallbackPresentInBufferLocation(c, v', addr, cb1, t1, b1) 
        && CallbackPresentInBufferLocation(c, v', addr, cb2, t2, b2)
      ) 
        ensures t1 == t2
        ensures ((cb1 == cb2) ==> b1 == b2)
        ensures !(cb1.OnEvict? && cb2.OnWriteBack?)
      {
        assert CallbackPresentInBufferLocation(c, v, addr, cb1, t1, b1);
        assert CallbackPresentInBufferLocation(c, v, addr, cb2, t2, b2);
      }
      assert UniqueTileForCallbackAddr(c, v');
    }
  }

  lemma PerformNextInstPreservesUniqueCurrentCallbacktoAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvPerfStore(c, v)
    ensures UniqueCurrentCallbacktoAddr(c, v')
  {
    if step.tile_step.CoreStep? {
      forall id: ThreadId | CurrentSpecCallbackId(c, v', id)
        ensures id.addr in v'.g.callback_epochs
        ensures id.count == v'.g.callback_epochs[id.addr].epoch
        ensures (v'.g.callback_epochs[id.addr].Miss? || v'.g.callback_epochs[id.addr].Evict?)
        ensures (v'.g.callback_epochs[id.addr].Miss? ==> id.cb.OnMiss?)
        ensures (v'.g.callback_epochs[id.addr].Evict? && !v'.g.callback_epochs[id.addr].dirty ==> id.cb.OnEvict?)
        ensures (v'.g.callback_epochs[id.addr].Evict? && v'.g.callback_epochs[id.addr].dirty ==> id.cb.OnWriteBack?)
      {
        assert CurrentSpecCallbackId(c, v, id);
      }
    } else {
      assert step.tile_step.EngineStep?;
      forall id: ThreadId | CurrentSpecCallbackId(c, v', id)
        ensures id.addr in v'.g.callback_epochs
        ensures id.count == v'.g.callback_epochs[id.addr].epoch
        ensures (v'.g.callback_epochs[id.addr].Miss? || v'.g.callback_epochs[id.addr].Evict?)
        ensures (v'.g.callback_epochs[id.addr].Miss? ==> id.cb.OnMiss?)
        ensures (v'.g.callback_epochs[id.addr].Evict? && !v'.g.callback_epochs[id.addr].dirty ==> id.cb.OnEvict?)
        ensures (v'.g.callback_epochs[id.addr].Evict? && v'.g.callback_epochs[id.addr].dirty ==> id.cb.OnWriteBack?)
      {
        var cur_addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
        var cur_cb := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
        var cur_id: ThreadId := CallbackId(cur_addr, cur_cb, v.g.callback_epochs[cur_addr].epoch);
        assert CallbackRunningInBufferLocation(c, v, cur_addr, cur_cb, step.tile_idx, step.tile_step.eng_step.idx);
      }
    }
  }

  lemma PerformNextInstPreservesCurrentCallbackIsRunning(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvPerfStore(c, v)
    ensures CurrentCallbackIsRunning(c, v')
  {
    if step.tile_step.CoreStep? {
      forall id: ThreadId | CurrentSpecCallbackId(c, v', id)
        ensures CallbackRunning(c, v', id.addr, id.cb)
      {
        assert CurrentSpecCallbackId(c, v, id);
        assert CallbackRunning(c, v, id.addr, id.cb);
        assert CallbackRunning(c, v', id.addr, id.cb) by {
          reveal CallbackRunning;
          var tile, buf :| CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile, buf);
          assert CallbackRunningInBufferLocation(c, v', id.addr, id.cb, tile, buf);
        }
      }
    } else {
      assert step.tile_step.EngineStep?;
      forall id: ThreadId | CurrentSpecCallbackId(c, v', id)
        ensures CallbackRunning(c, v', id.addr, id.cb)
      {
        var cur_addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
        var cur_cb := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
        var cur_id: ThreadId := CallbackId(cur_addr, cur_cb, v.g.callback_epochs[cur_addr].epoch);
        if id == cur_id {
          assert CallbackRunningInBufferLocation(c, v', id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackRunning;
          assert CallbackRunning(c, v', id.addr, id.cb);
        } else {
          assert CurrentSpecCallbackId(c, v, id);
          assert CallbackRunning(c, v, id.addr, id.cb);
          assert CallbackRunning(c, v', id.addr, id.cb) by {
            reveal CallbackRunning;
            var tile, buf :| CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile, buf);
            assert CallbackRunningInBufferLocation(c, v', id.addr, id.cb, tile, buf);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesEachAddrInEngineIsInCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvCorrectCore(c, v)
    ensures EachAddrInEngineIsInCorrectCore(c, v')
  {}

  lemma PerformNextInstPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma PerformNextInstPreservesL3MorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvCorrectCore(c, v)
    ensures L3MorphAddressesAreCorrectCore(c, v')
  {}

  lemma PerformNextInstPreservesL2PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvCorrectCore(c, v)
    ensures L2PrivateMorphAddressesAreCorrectCore(c, v')
  {}
  
  lemma PerformNextInstPreservesL1PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvCorrectCore(c, v)
    ensures L1PrivateMorphAddressesAreCorrectCore(c, v')
  {}

  lemma PerformNextInstPreservesEL1PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvCorrectCore(c, v)
    ensures EL1PrivateMorphAddressesAreCorrectCore(c, v')
  {}

  lemma PerformNextInstPreservesProxyPrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvCorrectCore(c, v)
    ensures ProxyPrivateMorphAddressesAreCorrectCore(c, v')
  {}

  lemma PerformNextInstPreservesL1AddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L1AddressesUnique(c, v)
    ensures L1AddressesUnique(c, v')
  {}

  lemma PerformNextInstPreservesEL1AddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EL1AddressesUnique(c, v)
    ensures EL1AddressesUnique(c, v')
  {}

  lemma PerformNextInstPreservesProxyAddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires ProxyAddressesUnique(c, v)
    ensures ProxyAddressesUnique(c, v')
  {}

  lemma PerformNextInstPreservesL2AddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2AddressesUnique(c, v)
    ensures L2AddressesUnique(c, v')
  {}

  lemma PerformNextInstPreservesL3AddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L3AddressesUnique(c, v)
    ensures L3AddressesUnique(c, v')
  {}

  lemma PerformNextInstPreservesNoDupIdxsInCBOrderTracker(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires NoDupIdxsInCBOrderTracker(c, v)
    ensures NoDupIdxsInCBOrderTracker(c, v')
  {}

  lemma PerformNextInstPreservesUnstartedBufferEntryWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires UnstartedBufferEntryWellformed(c, v)
    ensures UnstartedBufferEntryWellformed(c, v')
  {
    forall tile: nat, buf: nat | IsUnstartedBufferEntry(c, v', tile, buf)
      ensures (
        && var entry := v'.tiles[tile].engine.buffer[buf];
        && match entry.cb_type {
          case OnEvict(_) => entry.addr in c.program.onEvictCBs
          case OnWriteBack(_) => entry.addr in c.program.onWBCBs
          case OnMiss(_) => entry.addr in c.program.onMissCBs
        }
        && var regs := if entry.cb_type.OnMiss? then map[] else map[ EvictReg() := entry.cb_type.val ];
        && ValuesMatchForCallbackId(c, v', RuntimeData(PC(0, 0), regs, []), tile, buf)
      )
    {}
  }

  lemma PerformNextInstPreservesExistingCallbackIdsHaveCorrectEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires ExistingCallbackIdsHaveCorrectEpoch(c, v)
    ensures ExistingCallbackIdsHaveCorrectEpoch(c, v')
  {}


  lemma PerformNextInstPreservesOnlyHeadOfCBOrderTrackerIsRunning(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    ensures OnlyHeadOfCBOrderTrackerIsRunning(c, v')
  {
    forall addr: Address, tile: nat, buf: nat, cb | CallbackRunningInBufferLocation(c, v', addr, cb, tile, buf)
      ensures CBOrderTrackerValidIndex(c, v', addr, tile, 0)
      ensures buf == v'.tiles[tile].engine.cb_order[addr][0]
      ensures IsBufferEntry(c, v', tile, buf)
      ensures cb == EngReqToCBType(v'.tiles[tile].engine.buffer[buf].cb_type)
    {
      assert CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf);
    }
  }
  
  lemma PerformNextInstPreservesMorphWorkingSetInEpochs(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires MorphWorkingSetInEpochs(c, v)
    ensures MorphWorkingSetInEpochs(c, v')
  {}

  lemma PerformNextInstPreservesPendingMemMeansNonMorphAddress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires PendingMemMeansNonMorphAddress(c, v)
    ensures PendingMemMeansNonMorphAddress(c, v')
  {}
  
  lemma PerformNextInstPreservesPreMStateMeansNotDirtyCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires PreMStateMeansNotDirtyCore(c, v)
    ensures PreMStateMeansNotDirtyCore(c, v')
  {}

  lemma PerformNextInstPreservesPreMStateMeansNotDirtyEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires PreMStateMeansNotDirtyEngine(c, v)
    ensures PreMStateMeansNotDirtyEngine(c, v')
  {}

  lemma PerformNextInstPreservesPreMStateMeansNotDirtyL2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires PreMStateMeansNotDirtyL2(c, v)
    ensures PreMStateMeansNotDirtyL2(c, v')
  {}

  // lemma PerformNextInstPreservesL2EvictingOrPreDataCoherenceMeansDirI(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
  //   requires Tako.NextStep(c, v, v', step, re)
  //   requires step.TileStep?
  //   requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
  //   requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
  //   requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
  //   requires L2EvictingOrPreDataCoherenceMeansDirI(c, v)
  //   ensures L2EvictingOrPreDataCoherenceMeansDirI(c, v')
  // {}

  lemma PerformNextInstPreservesL2DirMorSDMeansL2CohM(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2DirMorSDMeansL2CohM(c, v)
    ensures L2DirMorSDMeansL2CohM(c, v')
  {}
  
  lemma PerformNextInstPreservesL2NotDirIMeansLoadableCoh(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2NotDirIMeansLoadableCoh(c, v)
    ensures L2NotDirIMeansLoadableCoh(c, v')
  {}

  lemma PerformNextInstPreservesPrivateMorphInL2IsCohM(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires PrivateMorphInL2IsCohM(c, v)
    ensures PrivateMorphInL2IsCohM(c, v')
  {}

  lemma PerformNextInstPreservesEpochEntryInMorphWorkingSet(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EpochEntryInMorphWorkingSet(c, v)
    ensures EpochEntryInMorphWorkingSet(c, v')
  {}
  

  import opened NetworkDiffCBsProof
  import opened OnMissInProgressPrivateProof
  import opened OnEvictInProgressPrivateProof
  import opened OnWritebackInProgressPrivateProof
  import opened OnMissInProgressSharedProof
  import opened OnEvictInProgressSharedProof
  import opened OnWritebackInProgressSharedProof
  import opened EngineBoundMsgUniqueCBProof
  import opened OnMissRequestOneSpotProof
  import opened OnMissResponseNoEvictProof
  import opened OnMissResponseNoWritebackProof
  import opened CBHeadMissNoEvictProof
  import opened CBHeadMissNoWritebackProof
  import opened MsgQueueHeadNoEvictProof
  import opened MsgQueueHeadNoWritebackProof
  import opened UniqueCacheBoundMsgProof
  import opened CBOrderTrackerWFProof
  import opened EngReqPropertiesProof
  import opened OutEpochDefnProof
  import opened InEpochDefnProof
  import opened OnEvictInProgressLoadableProof
  import opened OnWritebackInProgressLoadableProof
  import opened AddrInCacheLoadableProof
  import opened CBOrderTrackerEpochProof
  import opened L2DirectoryILoadableProof
  import opened DirtyBitMatchesEpochProof
  import opened DirtyBitPropertiesProof
  import opened CohMsgWellFormedProof
  
  import opened OnEvictLastWriteProofs
  import opened OnWritebackLastWriteProofs

  import opened WritesToAddrProofs

  lemma PerformNextInstPreservesInvPerfStore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvPerfStore(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesWF(c, v, v', step, re);
    PerformNextInstPreservesCoreRuntimeDataMatchesWithGhostRuntimeData(c, v, v', step, re);
    PerformNextInstPreservesRunningCallbackValuesAgree(c, v, v', step, re);
    PerformNextInstPreservesUniqueTileForCallbackAddr(c, v, v', step, re);
    PerformNextInstPreservesUniqueCurrentCallbacktoAddr(c, v, v', step, re);
    PerformNextInstPreservesCurrentCallbackIsRunning(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvCorrectCore(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesWF(c, v, v', step, re);
    PerformNextInstPreservesEachAddrInEngineIsInCorrectCore(c, v, v', step, re);
    PerformNextInstPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step, re);
    PerformNextInstPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step, re);
    PerformNextInstPreservesL2PrivateMorphAddressesAreCorrectCore(c, v, v', step, re);
    PerformNextInstPreservesL3MorphAddressesAreCorrectCore(c, v, v', step, re);
    PerformNextInstPreservesL1PrivateMorphAddressesAreCorrectCore(c, v, v', step, re);
    PerformNextInstPreservesEL1PrivateMorphAddressesAreCorrectCore(c, v, v', step, re);
    PerformNextInstPreservesProxyPrivateMorphAddressesAreCorrectCore(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvAddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvAddressesUnique(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesL1AddressesUnique(c, v, v', step, re);
    PerformNextInstPreservesEL1AddressesUnique(c, v, v', step, re);
    PerformNextInstPreservesProxyAddressesUnique(c, v, v', step, re);
    PerformNextInstPreservesL2AddressesUnique(c, v, v', step, re);
    PerformNextInstPreservesL3AddressesUnique(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvCallbackProgress_1(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures v'.WF(c)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
    ensures ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v')
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesWF(c, v, v', step, re);
    PerformNextInstPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step, re);
    PerformNextInstPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step, re);
    PerformNextInstPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step, re);
    PerformNextInstPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step, re);
    PerformNextInstPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step, re);
    PerformNextInstPreservesExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v, v', step, re);
    PerformNextInstPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step, re);
    PerformNextInstPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvCallbackProgress_2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
    ensures OnMissRequestOnlyRequestOrResponse(c, v')

    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')

    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step, re);
    PerformNextInstPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step, re);
    PerformNextInstPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step, re);

    PerformNextInstPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step, re);
    PerformNextInstPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step, re);
    PerformNextInstPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step, re);

    PerformNextInstPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step, re);
    PerformNextInstPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step, re);
    PerformNextInstPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvCallbackProgress_3(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)

    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
    ensures NoDupIdxsInCBOrderTracker(c, v')

    ensures EachAddrCacheBoundMsgIsUnique(c, v')
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesL2AddressesUnique(c, v, v', step, re);
    PerformNextInstPreservesL3AddressesUnique(c, v, v', step, re);

    PerformNextInstPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    PerformNextInstPreservesNoDupIdxsInCBOrderTracker(c, v, v', step, re);

    PerformNextInstPreservesEachAddrCacheBoundMsgIsUnique(c, v, v', step, re);
    PerformNextInstPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvCallbackProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvCallbackProgress(c, v')
  {
    PerformNextInstPreservesInvCallbackProgress_1(c, v, v', re);
    PerformNextInstPreservesInvCallbackProgress_2(c, v, v', re);
    PerformNextInstPreservesInvCallbackProgress_3(c, v, v', re);
  }
  
  lemma PerformNextInstPreservesInvStartCallback(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvStartCallback(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesWF(c, v, v', step, re);
    PerformNextInstPreservesUnstartedBufferEntryWellformed(c, v, v', step, re);
    PerformNextInstPreservesExistingCallbackIdsHaveCorrectEpoch(c, v, v', step, re);
    PerformNextInstPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step, re);
    PerformNextInstPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step, re);
    PerformNextInstPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvEpochs(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvEpochs(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step, re);
    PerformNextInstPreservesOnlyHeadOfCBOrderTrackerIsRunning(c, v, v', step, re);
    PerformNextInstPreservesMorphWorkingSetInEpochs(c, v, v', step, re);
    PerformNextInstPreservesEpochEntryInMorphWorkingSet(c, v, v', step, re);
    PerformNextInstPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step, re);
    PerformNextInstPreservesPendingMemMeansNonMorphAddress(c, v, v', step, re);
    PerformNextInstPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step, re);
    PerformNextInstPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvDirtyBit1(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures L2DirtyBitTracksInterveningWrite(c, v')
    ensures L3DirtyBitTracksInterveningWrite(c, v')

    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')

    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')

    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')

    ensures DirtyMorphAddressMeansInterveningWriteCore(c, v')
    ensures DirtyMorphAddressMeansInterveningWriteEngine(c, v')
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesL2DirtyBitTracksInterveningWrite(c, v, v', step, re);
    PerformNextInstPreservesL3DirtyBitTracksInterveningWrite(c, v, v', step, re);

    PerformNextInstPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step, re);
    PerformNextInstPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step, re);

    PerformNextInstPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step, re);
    PerformNextInstPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step, re);
    PerformNextInstPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step, re);
    PerformNextInstPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step, re);

    PerformNextInstPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step, re);
    PerformNextInstPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step, re);

    PerformNextInstPreservesDirtyMorphAddressMeansInterveningWriteCore(c, v, v', step, re);
    PerformNextInstPreservesDirtyMorphAddressMeansInterveningWriteEngine(c, v, v', step, re);
    PerformNextInstPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvDirtyBit2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v')
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v')
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')

    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')

    ensures PreMStateMeansNotDirtyCore(c, v')
    ensures PreMStateMeansNotDirtyEngine(c, v')
    ensures PreMStateMeansNotDirtyL2(c, v')

    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);

    PerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v, v', step, re);
    PerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v, v', step, re);
    PerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step, re);
    PerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step, re);
    
    PerformNextInstPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step, re);
    PerformNextInstPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step, re);
    PerformNextInstPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step, re);
    PerformNextInstPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step, re);

    PerformNextInstPreservesPreMStateMeansNotDirtyCore(c, v, v', step, re);
    PerformNextInstPreservesPreMStateMeansNotDirtyEngine(c, v, v', step, re);
    PerformNextInstPreservesPreMStateMeansNotDirtyL2(c, v, v', step, re);

    PerformNextInstPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step, re);
    PerformNextInstPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step ,re);
    PerformNextInstPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step, re);
    PerformNextInstPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step, re);
  }
  
  lemma PerformNextInstPreservesInvDirtyBit(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvDirtyBit(c, v')
  {
    PerformNextInstPreservesInvDirtyBit1(c, v, v', re);
    PerformNextInstPreservesInvDirtyBit2(c, v, v', re);
  }

  lemma PerformNextInstPreservesInvCoherenceState(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvCoherenceState(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step, re);
    PerformNextInstPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step, re);

    assume {:axiom} L2DirISMatchesLastWrite(c, v');
    assume {:axiom} L3DirISMatchesLastWrite(c, v');

    assume {:axiom} CoreLoadableMatchesLastWriteMorph(c, v');
    assume {:axiom} EngineLoadableMatchesLastWriteMorph(c, v');

    assume {:axiom} CoreLoadableMatchesLastWriteRegular(c, v');
    assume {:axiom} EngineLoadableMatchesLastWriteRegular(c, v');

    PerformNextInstPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step, re);
    PerformNextInstPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step, re);
    PerformNextInstPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step, re);

    PerformNextInstPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step, re);
    PerformNextInstPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step, re);
    PerformNextInstPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step, re);
    
    assume {:axiom} L2DirectoryInIMeansNoLoadableInCore(c, v');
    assume {:axiom} L2DirectoryInIMeansNoLoadableInEngine(c, v');
    assume {:axiom} L2DirectoryInIMeansNoLoadableInProxy(c, v');
  
    assume {:axiom} L2DirectoryInSMeansNoMInCore(c, v');
    assume {:axiom} L2DirectoryInSMeansNoMInEngine(c, v');
    assume {:axiom} L3DirectoryInSMeansNoMInL2(c, v');
  
    assume {:axiom} L2DirectoryInSDAndMInCoreMeansFormerOwner(c, v');
    assume {:axiom} L2DirectoryInSDAndMInEngineMeansFormerOwner(c, v');

    assume {:axiom} L2DirectoryInMAndMInCoreMeansOwnerOrFwdGetMInFlight(c, v');
    assume {:axiom} L2DirectoryInMAndMInEngineMeansOwnerOrFwdGetMInFlight(c, v');
  
    PerformNextInstPreservesL2AddrNotInCacheMeansNoLoadableInCore(c, v, v', step, re);
    PerformNextInstPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c, v, v', step, re);
    PerformNextInstPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c, v, v', step, re);

    assume {:axiom} L3AddrNotInCacheMeansL2AddrNotInCache(c, v');
    assume {:axiom} L3DirectoryInIMeansL2AddrNotInCache(c, v');

    assume {:axiom} L1InCohMMeansAddrNotInOtherL1s(c, v');
    assume {:axiom} EL1InCohMMeansAddrNotInOtherL1s(c, v');
    assume {:axiom} L2InCohMMeansAddrNotInOtherL2s(c, v');

    assume {:axiom} L1InCohMMeansNoT1DataInFlight(c, v');
    assume {:axiom} EL1InCohMMeansNoT1DataInFlight(c, v');

    assume {:axiom} MInCoreMeansMinL2(c, v');
    assume {:axiom} MInEngineMeansMinL2(c, v');
    
    PerformNextInstPreservesL2DirMorSDMeansL2CohM(c, v, v', step, re);
    PerformNextInstPreservesL2NotDirIMeansLoadableCoh(c, v, v', step, re);
    PerformNextInstPreservesPrivateMorphInL2IsCohM(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvWFMessages(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvWFMessages(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesWF(c, v, v', step, re);
    PerformNextInstPreservesL2QueueHeadsWellformed(c, v, v', step, re);
    PerformNextInstPreservesL3QueueHeadsWellformed(c, v, v', step, re);
    PerformNextInstPreservesMemMessagesWellformed(c, v, v', step, re);

    PerformNextInstPreservesL3DirOwnerIsAlwaysTier2Cache(c, v, v', step, re);
    PerformNextInstPreservesL3DirSharersAlwaysTier2Cache(c, v, v', step, re);
    PerformNextInstPreservesL2DirOwnerIsAlwaysTier1Cache(c, v, v', step, re);
    PerformNextInstPreservesL2DirSharersAlwaysTier1Cache(c, v, v', step, re);

    PerformNextInstPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step, re);
    PerformNextInstPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step, re);
    PerformNextInstPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step, re);
    PerformNextInstPreservesAllReqsToTier2HasTier1Source(c, v, v', step, re);
    PerformNextInstPreservesAllReqsToTier3HasTier2Source(c, v, v', step, re);
    PerformNextInstPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step, re);
    PerformNextInstPreservesAllDataToTier2FromCache(c, v, v', step, re);
    PerformNextInstPreservesAllDataToTier3FromTier2Cache(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInvCoherenceMessages(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvCoherenceMessages(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    assume {:axiom} PutMFromOwnerMeansNoLoadableInCore(c, v');
    assume {:axiom} PutMFromOwnerMeansNoLoadableInEngine(c, v');

    assume {:axiom} PutMInFlightMeansSourceIsEvicting(c, v');
    assume {:axiom} GetMInFlightMeansSourceIsTransitioningToM(c, v');
    assume {:axiom} FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v');
    assume {:axiom} GetSInFlightToT2MeansSourceIsTransitioningToS(c, v');
    assume {:axiom} FwdGetSInFlightToT1MeansSourceIsTransitioningToS(c, v');
    assume {:axiom} FwdGetSInFlightMeansDirectoryIsSD(c, v');
    assume {:axiom} FwdGetSInFlightMeansSrcDstDifferent(c, v');
  
    assume {:axiom} DataInFlightToT1MeansDirectoryNotInI(c, v');
    
    assume {:axiom} DataInFlightToT2FromT1MeansDirectoryInSD(c, v');
    assume {:axiom} DataInFlightToT3FromT2MeansDirectoryInSD(c, v');

    assume {:axiom} NoGetSAndReturningData(c, v');
    assume {:axiom} NoGetMAndReturningData(c, v');

    assume {:axiom} NoGetsAndDirML2(c, v');
  }

  lemma PerformNextInstPreservesInvPerfLoad(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures InvPerfLoad(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    PerformNextInstPreservesAddrInEpochMeansEventsWellformed(c, v, v', step, re);
    PerformNextInstPreservesAddrInEpochMeansEventsMatchAddrAtomicity(c, v, v', step, re);
    PerformNextInstPreservesWritesToAddrWellFormed(c, v, v', step, re);
    PerformNextInstPreservesAllWritesInWritesToAddr(c, v, v', step, re);
    PerformNextInstPreservesMoDeterminedByWritesToAddrOrder(c, v, v', step, re);
    PerformNextInstPreservesAllMoInWritesToAddr(c, v, v', step, re);
    PerformNextInstPreservesAllWritesToAddrLessThanCurrentPCCore(c, v, v', step, re);
    PerformNextInstPreservesAllWritesToAddrLessThanCurrentPCEngine(c, v, v', step, re);
    PerformNextInstPreservesWritesToAddrHaveValidThreadIds(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesInv(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == PerformStore || re == PerformRMW || re == PerformLoad || re == PerformBranch || re == PerformFlush
    requires Inv(c, v)
    ensures Inv(c, v')
  {
    PerformNextInstPreservesInvAddressesUnique(c, v, v', re);
    PerformNextInstPreservesInvPerfStore(c, v, v', re);
    PerformNextInstPreservesInvCorrectCore(c, v, v', re);
    PerformNextInstPreservesInvCallbackProgress(c, v, v', re);
    PerformNextInstPreservesInvStartCallback(c, v, v', re);
    PerformNextInstPreservesInvEpochs(c, v, v', re);
    PerformNextInstPreservesInvDirtyBit(c, v, v', re);
    PerformNextInstPreservesInvWFMessages(c, v, v', re);
    PerformNextInstPreservesInvCoherenceState(c, v, v', re);
    PerformNextInstPreservesInvCoherenceMessages(c, v, v', re);
    PerformNextInstPreservesInvPerfLoad(c, v, v', re);
  }
}