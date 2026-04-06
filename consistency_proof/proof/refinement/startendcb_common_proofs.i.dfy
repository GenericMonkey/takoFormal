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

module StartEndCBCommonProofs {
  import opened Types
  import opened TakoRefinementDefns
  import opened RefinementTypes
  import opened Execution
  import opened EngineTypes

  lemma StartEndCBPreservesWF(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires v.WF(c)
    ensures v'.WF(c)
  {}

  lemma StartEndCBPreservesCoreRuntimeDataMatchesWithGhostRuntimeData(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvPerfStore(c, v)
    ensures CoreRuntimeDataMatchesWithGhostRuntimeData(c, v')
  {
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

  // split
  lemma StartCBPreservesRunningCallbackValuesAgree(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires InvPerfStore(c, v)
    ensures RunningCallbackValuesAgree(c, v')
  {
    assert step.tile_step.EngineStep?;
    forall addr, cb, tile: nat, buf: nat | CallbackRunningInBufferLocation(c, v', addr, cb, tile, buf)
      ensures (
        && addr in v'.g.callback_epochs
        && var id: ThreadId := CallbackId(addr, cb, v'.g.callback_epochs[addr].epoch);
        && CurrentSpecCallbackId(c, v', id)
        && Engine.IsNextCallback(c.tiles[tile].engine, v.tiles[tile].engine, buf)
        && ValuesMatchForCallbackId(c, v', v'.g.pcs[id], tile, buf)
      )
    {
      var cur_addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
      var cur_cb := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
      var cur_id: ThreadId := CallbackId(cur_addr, cur_cb, v.g.callback_epochs[cur_addr].epoch);
      if addr == cur_addr && cb == cur_cb {
        assert CallbackPresentInBufferLocation(c, v, addr, cb, step.tile_idx, step.tile_step.eng_step.idx);
        assert CallbackPresentInBufferLocation(c, v, addr, cb, tile, buf);
        assert ValuesMatchForCallbackId(c, v', v'.g.pcs[cur_id], tile, buf);
      } else {
        assert CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf);
      }
    }
  }

  lemma EndCBPreservesRunningCallbackValuesAgree(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires InvPerfStore(c, v)
    ensures RunningCallbackValuesAgree(c, v')
  {
    assert step.tile_step.EngineStep?;
    forall addr, cb, tile: nat, buf: nat | CallbackRunningInBufferLocation(c, v', addr, cb, tile, buf)
      ensures (
        && addr in v'.g.callback_epochs
        && var id: ThreadId := CallbackId(addr, cb, v'.g.callback_epochs[addr].epoch);
        && CurrentSpecCallbackId(c, v', id)
        && Engine.IsNextCallback(c.tiles[tile].engine, v.tiles[tile].engine, buf)
        && ValuesMatchForCallbackId(c, v', v'.g.pcs[id], tile, buf)
      )
    {
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      assert CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf);
      var id' := CallbackId(addr, cb, v'.g.callback_epochs[addr].epoch);
      assert addr != entry.addr by {
        if addr == entry.addr {
          assert CallbackPresentInBufferLocation(c, v, entry.addr, EngReqToCBType(entry.cb_type), step.tile_idx, step.tile_step.eng_step.idx);
          assert CallbackPresentInBufferLocation(c, v, entry.addr, cb, tile, buf);
          assert false;
        }
      }
      assert CurrentSpecCallbackId(c, v', id');
      assert ValuesMatchForCallbackId(c, v', v'.g.pcs[id'], tile, buf);
    }
  }

  lemma StartEndCBPreservesUniqueTileForCallbackAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvPerfStore(c, v)
    ensures UniqueTileForCallbackAddr(c, v')
  {
    assert step.tile_step.EngineStep?;
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

  lemma StartCBPreservesUniqueCurrentCallbacktoAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires InvPerfStore(c, v)
    ensures UniqueCurrentCallbacktoAddr(c, v')
  {
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
      if id.addr == cur_id.addr {
        if id != cur_id {
          assert CurrentSpecCallbackId(c, v, id);
          assert id.cb != cur_id.cb;
          assert CallbackRunning(c, v, id.addr, id.cb);
          reveal CallbackRunning;
          var tile, buf :| CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, id.addr, cur_cb, step.tile_idx, step.tile_step.eng_step.idx);
          assert tile == step.tile_idx;
          assert buf != step.tile_step.eng_step.idx;
          assert false;
        }
      } else {
        assert CurrentSpecCallbackId(c, v, id);
      }
    }
  }

  lemma EndCBPreservesUniqueCurrentCallbacktoAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires InvPerfStore(c, v)
    ensures UniqueCurrentCallbacktoAddr(c, v')
  {
    forall id: ThreadId | CurrentSpecCallbackId(c, v', id)
      ensures id.addr in v'.g.callback_epochs
      ensures id.count == v'.g.callback_epochs[id.addr].epoch
      ensures (v'.g.callback_epochs[id.addr].Miss? || v'.g.callback_epochs[id.addr].Evict?)
      ensures (v'.g.callback_epochs[id.addr].Miss? ==> id.cb.OnMiss?)
      ensures (v'.g.callback_epochs[id.addr].Evict? && !v'.g.callback_epochs[id.addr].dirty ==> id.cb.OnEvict?)
      ensures (v'.g.callback_epochs[id.addr].Evict? && v'.g.callback_epochs[id.addr].dirty ==> id.cb.OnWriteBack?)
    {
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      assert CallbackRunningInBufferLocation(c, v, entry.addr, EngReqToCBType(entry.cb_type), step.tile_idx, step.tile_step.eng_step.idx);
      if id.addr == entry.addr {
        var entry_id := CallbackId(entry.addr, EngReqToCBType(entry.cb_type), v.g.callback_epochs[entry.addr].epoch);
        assert CurrentSpecCallbackId(c, v, id);
        assert CurrentSpecCallbackId(c, v, entry_id);
      }
    }
  }

  lemma StartCBPreservesCurrentCallbackIsRunning(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires InvPerfStore(c, v)
    ensures CurrentCallbackIsRunning(c, v')
  {
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
      } else {
        assert CurrentSpecCallbackId(c, v, id);
        assert CallbackRunning(c, v', id.addr, id.cb) by {
          reveal CallbackRunning;
          var tile, buf :| CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile, buf);
          assert CallbackRunningInBufferLocation(c, v', id.addr, id.cb, tile, buf);
        }
      }
    }
  }

  lemma EndCBPreservesCurrentCallbackIsRunning(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires InvPerfStore(c, v)
    ensures CurrentCallbackIsRunning(c, v')
  {
    assert step.tile_step.EngineStep?;
    forall id: ThreadId | CurrentSpecCallbackId(c, v', id)
      ensures CallbackRunning(c, v', id.addr, id.cb)
    {
      var cur_addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
      var cur_cb := EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
      var cur_id: ThreadId := CallbackId(cur_addr, cur_cb, v.g.callback_epochs[cur_addr].epoch);
      if id == cur_id {
        assert false;
      } else {
        assert CurrentSpecCallbackId(c, v, id);
        assert CallbackRunning(c, v', id.addr, id.cb) by {
          reveal CallbackRunning;
          var tile, buf :| CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile, buf);
          assert CallbackRunningInBufferLocation(c, v', id.addr, id.cb, tile, buf);
        }
      }
    }
  }

  lemma StartEndCBPreservesEachAddrInEngineIsInCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvCorrectCore(c, v)
    ensures EachAddrInEngineIsInCorrectCore(c, v')
  {}

  lemma StartEndCBPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma StartEndCBPreservesL3MorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvCorrectCore(c, v)
    ensures L3MorphAddressesAreCorrectCore(c, v')
  {}

  lemma StartEndCBPreservesL2PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvCorrectCore(c, v)
    ensures L2PrivateMorphAddressesAreCorrectCore(c, v')
  {}

  lemma StartEndCBPreservesL1PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvCorrectCore(c, v)
    ensures L1PrivateMorphAddressesAreCorrectCore(c, v')
  {}

  lemma StartEndCBPreservesEL1PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvCorrectCore(c, v)
    ensures EL1PrivateMorphAddressesAreCorrectCore(c, v')
  {}

  lemma StartEndCBPreservesProxyPrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvCorrectCore(c, v)
    ensures ProxyPrivateMorphAddressesAreCorrectCore(c, v')
  {}

  lemma StartEndCBPreservesL1AddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L1AddressesUnique(c, v)
    ensures L1AddressesUnique(c, v')
  {}
  
  lemma StartEndCBPreservesEL1AddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EL1AddressesUnique(c, v)
    ensures EL1AddressesUnique(c, v')
  {}
  
  lemma StartEndCBPreservesProxyAddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires ProxyAddressesUnique(c, v)
    ensures ProxyAddressesUnique(c, v')
  {}

  lemma StartEndCBPreservesL2AddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2AddressesUnique(c, v)
    ensures L2AddressesUnique(c, v')
  {}

  lemma StartEndCBPreservesL3AddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L3AddressesUnique(c, v)
    ensures L3AddressesUnique(c, v')
  {}

  lemma StartEndCBPreservesNoDupIdxsInCBOrderTracker(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires NoDupIdxsInCBOrderTracker(c, v)
    ensures NoDupIdxsInCBOrderTracker(c, v')
  {}

  lemma StartEndCBPreservesUnstartedBufferEntryWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires UnstartedBufferEntryWellformed(c, v)
    ensures UnstartedBufferEntryWellformed(c, v')
  {}

  lemma StartEndCBPreservesExistingCallbackIdsHaveCorrectEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires ExistingCallbackIdsHaveCorrectEpoch(c, v)
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures ExistingCallbackIdsHaveCorrectEpoch(c, v')
  {}
  
  lemma StartEndCBPreservesOnlyHeadOfCBOrderTrackerIsRunning(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    ensures OnlyHeadOfCBOrderTrackerIsRunning(c, v')
  {
    forall addr: Address, tile: nat, buf: nat, cb | CallbackRunningInBufferLocation(c, v', addr, cb, tile, buf)
      ensures CBOrderTrackerValidIndex(c, v', addr, tile, 0)
      ensures buf == v'.tiles[tile].engine.cb_order[addr][0]
      ensures IsBufferEntry(c, v', tile, buf)
      ensures cb == EngReqToCBType(v'.tiles[tile].engine.buffer[buf].cb_type)
    {
      if !CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf) {
        assert CBOrderTrackerValidIndex(c, v', addr, tile, 0);
        assert buf == v'.tiles[tile].engine.cb_order[addr][0];
      } else {
        assert CBOrderTrackerValidIndex(c, v', addr, tile, 0);
        assert buf == v'.tiles[tile].engine.cb_order[addr][0];
      }
    }
  }
  
  lemma StartEndCBPreservesMorphWorkingSetInEpochs(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires MorphWorkingSetInEpochs(c, v)
    ensures MorphWorkingSetInEpochs(c, v')
  {}

  lemma StartEndCBPreservesPendingMemMeansNonMorphAddress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires PendingMemMeansNonMorphAddress(c, v)
    ensures PendingMemMeansNonMorphAddress(c, v')
  {}

  lemma StartEndCBPreservesPreMStateMeansNotDirtyCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires PreMStateMeansNotDirtyCore(c, v)
    ensures PreMStateMeansNotDirtyCore(c, v')
  {}

  lemma StartEndCBPreservesPreMStateMeansNotDirtyEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires PreMStateMeansNotDirtyEngine(c, v)
    ensures PreMStateMeansNotDirtyEngine(c, v')
  {}

  lemma StartEndCBPreservesPreMStateMeansNotDirtyL2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires PreMStateMeansNotDirtyL2(c, v)
    ensures PreMStateMeansNotDirtyL2(c, v')
  {}

  // lemma StartEndCBPreservesL2EvictingOrPreDataCoherenceMeansDirI(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
  //   requires Tako.NextStep(c, v, v', step, re)
  //   requires re == StartOnEvict
  //     || re == StartOnMiss
  //     || re == StartOnWriteback
  //     || re == EndOnEvict
  //     || re == EndOnMiss
  //     || re == EndOnWriteback
  //   requires L2EvictingOrPreDataCoherenceMeansDirI(c, v)
  //   ensures L2EvictingOrPreDataCoherenceMeansDirI(c, v')
  // {}

  lemma StartEndCBPreservesL2DirMorSDMeansL2CohM(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2DirMorSDMeansL2CohM(c, v)
    ensures L2DirMorSDMeansL2CohM(c, v')
  {}
  
  lemma StartEndCBPreservesL2NotDirIMeansLoadableCoh(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2NotDirIMeansLoadableCoh(c, v)
    ensures L2NotDirIMeansLoadableCoh(c, v')
  {}

  lemma StartEndCBPreservesPrivateMorphInL2IsCohM(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires PrivateMorphInL2IsCohM(c, v)
    ensures PrivateMorphInL2IsCohM(c, v')
  {}
  
  lemma StartEndCBPreservesEpochEntryInMorphWorkingSet(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
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

  lemma StartEndCBPreservesInvPerfStore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvPerfStore(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    StartEndCBPreservesWF(c, v, v', step, re);
    StartEndCBPreservesCoreRuntimeDataMatchesWithGhostRuntimeData(c, v, v', step, re);
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesRunningCallbackValuesAgree(c, v, v', step, re);
    } else {
      EndCBPreservesRunningCallbackValuesAgree(c, v, v', step, re);
    }
    StartEndCBPreservesUniqueTileForCallbackAddr(c, v, v', step, re);
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesUniqueCurrentCallbacktoAddr(c, v, v', step, re);
    } else {
      EndCBPreservesUniqueCurrentCallbacktoAddr(c, v, v', step, re);
    }
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesCurrentCallbackIsRunning(c, v, v', step, re);
    } else {
      EndCBPreservesCurrentCallbackIsRunning(c, v, v', step, re);
    }
  }

  lemma StartEndCBPreservesInvCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvCorrectCore(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    StartEndCBPreservesWF(c, v, v', step, re);
    StartEndCBPreservesEachAddrInEngineIsInCorrectCore(c, v, v', step, re);
    StartEndCBPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step, re);
    StartEndCBPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step, re);
    StartEndCBPreservesL2PrivateMorphAddressesAreCorrectCore(c, v, v', step, re);
    StartEndCBPreservesL3MorphAddressesAreCorrectCore(c, v, v', step, re);
    StartEndCBPreservesL1PrivateMorphAddressesAreCorrectCore(c, v, v', step, re);
    StartEndCBPreservesEL1PrivateMorphAddressesAreCorrectCore(c, v, v', step, re);
    StartEndCBPreservesProxyPrivateMorphAddressesAreCorrectCore(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvAddressesUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvAddressesUnique(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    StartEndCBPreservesL1AddressesUnique(c, v, v', step, re);
    StartEndCBPreservesEL1AddressesUnique(c, v, v', step, re);
    StartEndCBPreservesProxyAddressesUnique(c, v, v', step, re);
    StartEndCBPreservesL2AddressesUnique(c, v, v', step, re);
    StartEndCBPreservesL3AddressesUnique(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvCallbackProgress_1(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
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
    StartEndCBPreservesWF(c, v, v', step, re);
    StartEndCBPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step, re);
    StartEndCBPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step, re);
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step, re);
    } else {
      EndCBPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step, re);
    }
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step, re);
    } else {
      EndCBPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step, re);
    }
    StartEndCBPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step, re);
    StartEndCBPreservesExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v, v', step, re);
    StartEndCBPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step, re);
    StartEndCBPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvCallbackProgress_2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
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
    StartEndCBPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step, re);
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step, re);
    } else {
      EndCBPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step, re);
    }
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step, re);
    } else {
      EndCBPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step, re);
    }
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step, re);
    } else {
      EndCBPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step, re);
    }
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step, re);
    } else {
      EndCBPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step, re);
    }
    StartEndCBPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step, re);

    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step, re);
    } else {
      EndCBPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step, re);
    }
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step, re);
    } else {
      EndCBPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step, re);
    }
    StartEndCBPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvCallbackProgress_3(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)

    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
    ensures NoDupIdxsInCBOrderTracker(c, v')

    ensures EachAddrCacheBoundMsgIsUnique(c, v')
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    } else {
      EndCBPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    }
    StartEndCBPreservesNoDupIdxsInCBOrderTracker(c, v, v', step, re);

    StartEndCBPreservesL2AddressesUnique(c, v, v', step, re);
    StartEndCBPreservesL3AddressesUnique(c, v, v', step, re);

    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesEachAddrCacheBoundMsgIsUnique(c, v, v', step, re);
    } else {
      EndCBPreservesEachAddrCacheBoundMsgIsUnique(c, v, v', step, re);
    }
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step, re);
    } else {
      EndCBPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step, re);
    }
  }

  lemma StartEndCBPreservesInvCallbackProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvCallbackProgress(c, v')
  {
    StartEndCBPreservesInvCallbackProgress_1(c, v, v', re);
    StartEndCBPreservesInvCallbackProgress_2(c, v, v', re);
    StartEndCBPreservesInvCallbackProgress_3(c, v, v', re);
  }

  lemma StartEndCBPreservesInvStartCallback(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvStartCallback(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    StartEndCBPreservesWF(c, v, v', step, re);
    StartEndCBPreservesUnstartedBufferEntryWellformed(c, v, v', step, re);
    StartEndCBPreservesExistingCallbackIdsHaveCorrectEpoch(c, v, v', step, re);
    StartEndCBPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step, re);
    StartEndCBPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step, re);
    StartEndCBPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvEpochs(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvEpochs(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    StartEndCBPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step, re);
    StartEndCBPreservesOnlyHeadOfCBOrderTrackerIsRunning(c, v, v', step, re);
    StartEndCBPreservesMorphWorkingSetInEpochs(c, v, v', step, re);
    StartEndCBPreservesEpochEntryInMorphWorkingSet(c, v, v', step, re);
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step, re);
    } else {
      EndCBPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step, re);
    }
    StartEndCBPreservesPendingMemMeansNonMorphAddress(c, v, v', step, re);
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step, re);
    } else {
      EndCBPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step, re);
    }
    StartEndCBPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvDirtyBit1(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
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
    StartEndCBPreservesL2DirtyBitTracksInterveningWrite(c, v, v', step, re);
    StartEndCBPreservesL3DirtyBitTracksInterveningWrite(c, v, v', step, re);

    StartEndCBPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step, re);
    StartEndCBPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step, re);

    StartEndCBPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step, re);
    StartEndCBPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step, re);
    StartEndCBPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step, re);
    StartEndCBPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step, re);

    StartEndCBPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step, re);
    StartEndCBPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step, re);

    StartEndCBPreservesDirtyMorphAddressMeansInterveningWriteCore(c, v, v', step, re);
    StartEndCBPreservesDirtyMorphAddressMeansInterveningWriteEngine(c, v, v', step, re);
    StartEndCBPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvDirtyBit2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
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

    StartEndCBPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v, v', step, re);
    StartEndCBPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v, v', step, re);
    StartEndCBPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step, re);
    StartEndCBPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step, re);
    
    StartEndCBPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step, re);
    StartEndCBPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step, re);
    StartEndCBPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step, re);
    StartEndCBPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step, re);

    StartEndCBPreservesPreMStateMeansNotDirtyCore(c, v, v', step, re);
    StartEndCBPreservesPreMStateMeansNotDirtyEngine(c, v, v', step, re);
    StartEndCBPreservesPreMStateMeansNotDirtyL2(c, v, v', step, re);

    StartEndCBPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step, re);
    StartEndCBPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step, re);
    StartEndCBPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step, re);
    StartEndCBPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvDirtyBit(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvDirtyBit(c, v')
  {
    StartEndCBPreservesInvDirtyBit1(c, v, v', re);
    StartEndCBPreservesInvDirtyBit2(c, v, v', re);
  }

  lemma StartEndCBPreservesInvCoherenceState(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvCoherenceState(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    StartEndCBPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step, re);
    StartEndCBPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step, re);

    assume {:axiom} L2DirISMatchesLastWrite(c, v');
    assume {:axiom} L3DirISMatchesLastWrite(c, v');
  
    assume {:axiom} CoreLoadableMatchesLastWriteMorph(c, v');
    assume {:axiom} EngineLoadableMatchesLastWriteMorph(c, v');

    assume {:axiom} CoreLoadableMatchesLastWriteRegular(c, v');
    assume {:axiom} EngineLoadableMatchesLastWriteRegular(c, v');

    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step, re);
    } else {
      EndCBPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step, re);
    }
    StartEndCBPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step, re);
    StartEndCBPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step, re);

    StartEndCBPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step, re);
    StartEndCBPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step, re);
    StartEndCBPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step, re);
    
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
  
    StartEndCBPreservesL2AddrNotInCacheMeansNoLoadableInCore(c, v, v', step, re);
    StartEndCBPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c, v, v', step, re);
    StartEndCBPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c, v, v', step, re);

    assume {:axiom} L3AddrNotInCacheMeansL2AddrNotInCache(c, v');
    assume {:axiom} L3DirectoryInIMeansL2AddrNotInCache(c, v');

    assume {:axiom} L1InCohMMeansAddrNotInOtherL1s(c, v');
    assume {:axiom} EL1InCohMMeansAddrNotInOtherL1s(c, v');
    assume {:axiom} L2InCohMMeansAddrNotInOtherL2s(c, v');

    assume {:axiom} L1InCohMMeansNoT1DataInFlight(c, v');
    assume {:axiom} EL1InCohMMeansNoT1DataInFlight(c, v');

    assume {:axiom} MInCoreMeansMinL2(c, v');
    assume {:axiom} MInEngineMeansMinL2(c, v');
    
    StartEndCBPreservesL2DirMorSDMeansL2CohM(c, v, v', step, re);
    StartEndCBPreservesL2NotDirIMeansLoadableCoh(c, v, v', step, re);
    StartEndCBPreservesPrivateMorphInL2IsCohM(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvWFMessages(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvWFMessages(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    StartEndCBPreservesWF(c, v, v', step, re);
    StartEndCBPreservesL2QueueHeadsWellformed(c, v, v', step, re);
    StartEndCBPreservesL3QueueHeadsWellformed(c, v, v', step, re);
    StartEndCBPreservesMemMessagesWellformed(c, v, v', step, re);

    StartEndCBPreservesL3DirOwnerIsAlwaysTier2Cache(c, v, v', step, re);
    StartEndCBPreservesL3DirSharersAlwaysTier2Cache(c, v, v', step, re);
    StartEndCBPreservesL2DirOwnerIsAlwaysTier1Cache(c, v, v', step, re);
    StartEndCBPreservesL2DirSharersAlwaysTier1Cache(c, v, v', step, re);

    StartEndCBPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step, re);
    StartEndCBPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step, re);
    StartEndCBPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step, re);
    StartEndCBPreservesAllReqsToTier2HasTier1Source(c, v, v', step, re);
    StartEndCBPreservesAllReqsToTier3HasTier2Source(c, v, v', step, re);
    StartEndCBPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step, re);
    StartEndCBPreservesAllDataToTier2FromCache(c, v, v', step, re);
    StartEndCBPreservesAllDataToTier3FromTier2Cache(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInvCoherenceMessages(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
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

  lemma StartEndCBPreservesInvPerfLoad(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures InvPerfLoad(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, re);
    StartEndCBPreservesAddrInEpochMeansEventsWellformed(c, v, v', step, re);
    StartEndCBPreservesAddrInEpochMeansEventsMatchAddrAtomicity(c, v, v', step, re);
    StartEndCBPreservesWritesToAddrWellFormed(c, v, v', step, re);
    StartEndCBPreservesAllWritesInWritesToAddr(c, v, v', step, re);
    StartEndCBPreservesMoDeterminedByWritesToAddrOrder(c, v, v', step, re);
    StartEndCBPreservesAllMoInWritesToAddr(c, v, v', step, re);
    StartEndCBPreservesAllWritesToAddrLessThanCurrentPCCore(c, v, v', step, re);
    StartEndCBPreservesAllWritesToAddrLessThanCurrentPCEngine(c, v, v', step, re);
    StartEndCBPreservesWritesToAddrHaveValidThreadIds(c, v, v', step, re);
  }

  lemma StartEndCBPreservesInv(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires Inv(c, v)
    ensures Inv(c, v')
  {
    StartEndCBPreservesInvAddressesUnique(c, v, v', re);
    StartEndCBPreservesInvPerfStore(c, v, v', re);
    StartEndCBPreservesInvCorrectCore(c, v, v', re);
    StartEndCBPreservesInvCallbackProgress(c, v, v', re);
    StartEndCBPreservesInvStartCallback(c, v, v', re);
    StartEndCBPreservesInvEpochs(c, v, v', re);
    StartEndCBPreservesInvDirtyBit(c, v, v', re);
    StartEndCBPreservesInvWFMessages(c, v, v', re);
    StartEndCBPreservesInvCoherenceState(c, v, v', re);
    StartEndCBPreservesInvCoherenceMessages(c, v, v', re);
    StartEndCBPreservesInvPerfLoad(c, v, v', re);
  }
}
