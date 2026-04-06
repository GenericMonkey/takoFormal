include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"
include "refinement_defns.i.dfy"
include "invproofs/onmiss_private.i.dfy"
include "invproofs/onevict_private.i.dfy"
include "invproofs/onwb_private.i.dfy"
include "invproofs/onmiss_shared.i.dfy"
include "invproofs/onevict_shared.i.dfy"
include "invproofs/onwb_shared.i.dfy"
include "invproofs/engbound_unique.i.dfy"
include "invproofs/network_diff_cbs.i.dfy"
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

module NoOpRefinementProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma NoOpRefinement(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures TakoRefinementDefns.Inv(c, v')
    ensures VariablesAbstraction(c, v) == VariablesAbstraction(c, v')
  {
    NoOpValidRefinementStep(c, v, v');
    NoOpPreservesInv(c, v, v');
  }

  lemma NoOpValidRefinementStep(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    ensures VariablesAbstraction(c, v) == VariablesAbstraction(c, v')
  {}

  lemma NoOpPreservesWF(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    ensures v'.WF(c)
  {}

  ///////////////////////////////////////////////////////////////////////////////////
  // CoreRuntimeDataMatchesWithGhostRuntimeData
  ///////////////////////////////////////////////////////////////////////////////////
  lemma NoOpPreservesCoreRuntimeDataMatchesWithGhostRuntimeData(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvPerfStore(c, v)
    ensures CoreRuntimeDataMatchesWithGhostRuntimeData(c, v')
  {
    forall id: ThreadId | ValidSpecCoreId(c, v', id)
      ensures ThreadIdMatchesCoreId(c, v', id)
    {
      assert ValidSpecCoreId(c, v, id);
    }
  }

  ///////////////////////////////////////////////////////////////////////////////////
  // RunningCallbackValuesAgree
  ///////////////////////////////////////////////////////////////////////////////////
  lemma NoOpPreservesRunningCallbackValuesAgree(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvPerfStore(c, v)
    ensures RunningCallbackValuesAgree(c, v')
  {
    forall addr, cb, tile: nat, buf | CallbackRunningInBufferLocation(c, v', addr, cb, tile, buf)
      ensures (
        && addr in v'.g.callback_epochs
        && var id := CallbackId(addr, cb, v'.g.callback_epochs[addr].epoch);
        && CurrentSpecCallbackId(c, v', id)
        && Engine.IsNextCallback(c.tiles[tile].engine, v'.tiles[tile].engine, buf)
        && ValuesMatchForCallbackId(c, v', v.g.pcs[id], tile, buf)
      )
    {
      assert CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf);
    }
  }

  ///////////////////////////////////////////////////////////////////////////////////
  // UniqueTileForCallbackAddr
  ///////////////////////////////////////////////////////////////////////////////////
  lemma NoOpPreservesUniqueTileForCallbackAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvPerfStore(c, v) && InvCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures UniqueTileForCallbackAddr(c, v')
  {
    if step.TileStep? && step.tile_step.EngineStep? && step.tile_step.eng_step.ReceiveCallbackReqStep? {
      var cur_addr := step.msgOps.recv.val.meta.addr;
      var cur_cb := EngReqToCBType(step.msgOps.recv.val.engine_req);
      forall addr: Address, cb1: CallbackType, cb2: CallbackType, t1: nat, t2: nat, b1: nat, b2: nat | (
        && CallbackPresentInBufferLocation(c, v', addr, cb1, t1, b1)
        && CallbackPresentInBufferLocation(c, v', addr, cb2, t2, b2)
      )
        ensures t1 == t2
        ensures (cb1 == cb2 ==> b1 == b2)
        ensures !(cb1.OnEvict? && cb2.OnWriteBack?)

      {
        if CallbackPresentInBufferLocation(c, v, addr, cb1, t1, b1) &&
          CallbackPresentInBufferLocation(c, v, addr, cb2, t2, b2) {
          assert t1 == t2;
          assert (cb1 == cb2 ==> b1 == b2);
        } else {
          assert addr == cur_addr;
          if !CallbackPresentInBufferLocation(c, v, addr, cb1, t1, b1) {
            assert cur_cb == cb1;
            assert t1 == step.tile_idx;
            assert b1 == step.tile_step.eng_step.idx;
            if CallbackPresentInBufferLocation(c, v, addr, cb2, t2, b2) {
              assert step.tile_idx == t2;
              assert cur_cb != cb2;
            }
          } else {
            assert !CallbackPresentInBufferLocation(c, v, addr, cb2, t2, b2);
            assert cur_cb == cb2;
            assert t2 == step.tile_idx;
            assert b2 == step.tile_step.eng_step.idx;
            if CallbackPresentInBufferLocation(c, v, addr, cb1, t1, b1) {
              assert step.tile_idx == t1;
              assert cur_cb != cb1;
            }
          }
        }
      }
    } else {
      forall addr: Address, cb1: CallbackType, cb2: CallbackType, t1: nat, t2: nat, b1: nat, b2: nat | (
        && CallbackPresentInBufferLocation(c, v', addr, cb1, t1, b1)
        && CallbackPresentInBufferLocation(c, v', addr, cb2, t2, b2)
      )
        ensures t1 == t2
        ensures (cb1 == cb2 ==> b1 == b2)
        ensures !(cb1.OnEvict? && cb2.OnWriteBack?)
      {
        assert CallbackPresentInBufferLocation(c, v, addr, cb1, t1, b1);
        assert CallbackPresentInBufferLocation(c, v, addr, cb2, t2, b2);
      }
    }
  }

  ///////////////////////////////////////////////////////////////////////////////////
  // UniqueCurrentCallbacktoAddr
  ///////////////////////////////////////////////////////////////////////////////////
  lemma NoOpPreservesUniqueCurrentCallbacktoAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvPerfStore(c, v)
    ensures UniqueCurrentCallbacktoAddr(c, v')
  {}

  ///////////////////////////////////////////////////////////////////////////////////
  // CurrentCallbackIsRunning
  ///////////////////////////////////////////////////////////////////////////////////
  lemma NoOpPreservesCurrentCallbackIsRunning(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvPerfStore(c, v)
    ensures CurrentCallbackIsRunning(c, v')
  {
    forall id: ThreadId | CurrentSpecCallbackId(c, v', id)
      ensures CallbackRunning(c, v', id.addr, id.cb)
    {
      assert CurrentSpecCallbackId(c, v, id);
      assert CallbackRunning(c, v', id.addr, id.cb) by {
        reveal CallbackRunning;
        var tile, buf :| CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile, buf);
        assert CallbackRunningInBufferLocation(c, v', id.addr, id.cb, tile, buf);
      }
    }
  }

  ///////////////////////////////////////////////////////////////////////////////////
  // EachAddrInEngineIsInCorrectCore
  ///////////////////////////////////////////////////////////////////////////////////
  lemma NoOpPreservesEachAddrInEngineIsInCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvCorrectCore(c, v)
    ensures EachAddrInEngineIsInCorrectCore(c, v')
  {}


  ///////////////////////////////////////////////////////////////////////////////////
  // EachAddrInCacheBoundMsgHasCorrectCore
  ///////////////////////////////////////////////////////////////////////////////////
  lemma ProxyNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma CoreNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma EngineNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2DirectoryNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma L3NoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {}

  lemma NoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInCacheBoundMsgHasCorrectCore(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        assert EachAddrInCacheBoundMsgHasCorrectCore(c, v');
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
          }
        }
      }
    }
  }

  ///////////////////////////////////////////////////////////////////////////////////
  // L3MorphAddressesAreCorrectCore
  ///////////////////////////////////////////////////////////////////////////////////
  lemma NoOpPreservesL3MorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvCorrectCore(c, v)
    ensures L3MorphAddressesAreCorrectCore(c, v')
  {}

  ///////////////////////////////////////////////////////////////////////////////////
  // L2MorphAddressesAreCorrectCore
  ///////////////////////////////////////////////////////////////////////////////////
  lemma NoOpPreservesL2PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvCorrectCore(c, v)
    ensures L2PrivateMorphAddressesAreCorrectCore(c, v')
  {}

  lemma NoOpPreservesL1PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvCorrectCore(c, v)
    ensures L1PrivateMorphAddressesAreCorrectCore(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma NoOpPreservesEL1PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v)
    ensures EL1PrivateMorphAddressesAreCorrectCore(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma NoOpPreservesProxyPrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InvCorrectCore(c, v)
    ensures ProxyPrivateMorphAddressesAreCorrectCore(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma NoOpPreservesL1AddressesUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L1AddressesUnique(c, v)
    ensures L1AddressesUnique(c, v')
  {}

  lemma NoOpPreservesEL1AddressesUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EL1AddressesUnique(c, v)
    ensures EL1AddressesUnique(c, v')
  {
    if step.TileStep? && step.tile_step.EngineStep? {
      assert EL1AddressesUnique(c, v');
    } else {
      assert EL1AddressesUnique(c, v);
    }
  }

  lemma NoOpPreservesProxyAddressesUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires ProxyAddressesUnique(c, v)
    ensures ProxyAddressesUnique(c, v')
  {}

  // TODO: Adding body here drastically improves perf. investigate why
  lemma NoOpPreservesL2AddressesUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2AddressesUnique(c, v)
    ensures L2AddressesUnique(c, v')
  {
    if step.TileStep? && step.tile_step.L2Step? {
      assert L2AddressesUnique(c, v');
    } else {
      assert L2AddressesUnique(c, v);
    }
  }

  lemma NoOpPreservesL3AddressesUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L3AddressesUnique(c, v)
    ensures L3AddressesUnique(c, v')
  {
    if step.TileStep? && step.tile_step.L3Step? {
      assert L3AddressesUnique(c, v');
    } else {
      assert L3AddressesUnique(c, v);
    }
  }

  lemma NoOpPreservesNoDupIdxsInCBOrderTracker(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires NoDupIdxsInCBOrderTracker(c, v)
    ensures NoDupIdxsInCBOrderTracker(c, v')
  {
    forall addr: Address, t: nat, idx1: nat, idx2: nat |
      (
        && CBOrderTrackerValidIndex(c, v', addr, t, idx1)
        && CBOrderTrackerValidIndex(c, v', addr, t, idx2)
        && v'.tiles[t].engine.cb_order[addr][idx1] == v'.tiles[t].engine.cb_order[addr][idx2]
      )
    ensures
      idx1 == idx2
    {
      if CBOrderTrackerValidIndex(c, v, addr, t, idx1) && CBOrderTrackerValidIndex(c, v, addr, t, idx2) {
        assert idx1 == idx2;
      } else {
        if CBOrderTrackerValidIndex(c, v, addr, t, idx1) {
          assert v.tiles[t].engine.cb_order[addr][idx1] in v.tiles[t].engine.cb_order[addr];
          assert idx1 == idx2;
        } else if CBOrderTrackerValidIndex(c, v, addr, t, idx2) {
          assert v.tiles[t].engine.cb_order[addr][idx2] in v.tiles[t].engine.cb_order[addr];
          assert idx1 == idx2;
        } else {
          assert idx1 == idx2;
        }
      }
    }
  }

  lemma NoOpPreservesUnstartedBufferEntryWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    requires UnstartedBufferEntryWellformed(c, v)
    ensures UnstartedBufferEntryWellformed(c, v')
  {
    if step.TileStep? && step.tile_step.EngineStep? {
      assert UnstartedBufferEntryWellformed(c, v');
    }
  }

  lemma NoOpPreservesExistingCallbackIdsHaveCorrectEpoch(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires ExistingCallbackIdsHaveCorrectEpoch(c, v)
    ensures ExistingCallbackIdsHaveCorrectEpoch(c, v')
  {}

  
  lemma NoOpPreservesOnlyHeadOfCBOrderTrackerIsRunning(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
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

  lemma NoOpPreservesMorphWorkingSetInEpochs(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires MorphWorkingSetInEpochs(c, v)
    ensures MorphWorkingSetInEpochs(c, v')
  {}

  lemma NoOpPreservesPendingMemMeansNonMorphAddress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires PendingMemMeansNonMorphAddress(c, v)
    ensures PendingMemMeansNonMorphAddress(c, v')
  {}

  lemma NoOpPreservesPreMStateMeansNotDirtyCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires PreMStateMeansNotDirtyCore(c, v)
    ensures PreMStateMeansNotDirtyCore(c, v')
  {}

  lemma NoOpPreservesPreMStateMeansNotDirtyEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires PreMStateMeansNotDirtyEngine(c, v)
    ensures PreMStateMeansNotDirtyEngine(c, v')
  {}

  lemma NoOpPreservesPreMStateMeansNotDirtyL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires NoGetsAndDirML2(c, v)
    requires PreMStateMeansNotDirtyL2(c, v)
    ensures PreMStateMeansNotDirtyL2(c, v')
  {
    if step.TileStep? && step.tile_step.L2Step? && step.tile_step.l2_step.DirectoryStep? {
      if step.tile_step.l2_step.msg.coh_msg.GetM? 
        && v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.M?
        && step.tile_step.l2_step.msg.meta.src == Cache(step.tile_idx, Proxy)
      {
        assert GetMInFlight(c, v, v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].addr, step.tile_step.l2_step.msg.meta.src, Cache(step.tile_idx, L2)) by {
          reveal GetMInFlight;
        }
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.owner != Cache(step.tile_idx, Proxy);
      } else if step.tile_step.l2_step.msg.coh_msg.GetS? 
        && v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.M? 
        && step.tile_step.l2_step.msg.meta.src == Cache(step.tile_idx, Proxy)
      {
        assert GetSInFlight(c, v, v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].addr, step.tile_step.l2_step.msg.meta.src, Cache(step.tile_idx, L2)) by {
          reveal GetSInFlight;
        }
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.owner != Cache(step.tile_idx, Proxy);
      } 
    }
  }

  // lemma NoOpPreservesL2EvictingOrPreDataCoherenceMeansDirI(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
  //   requires Tako.NextStep(c, v, v', step, NoOp)
  //   requires L2EvictingOrPreDataCoherenceMeansDirI(c, v)
  //   ensures L2EvictingOrPreDataCoherenceMeansDirI(c, v')
  // {}

  lemma NoOpPreservesL2DirMorSDMeansL2CohM(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirMorSDMeansL2CohM(c, v)
    ensures L2DirMorSDMeansL2CohM(c, v')
  {
    if step.TileStep? && step.tile_step.L2Step? {
      assert L2DirMorSDMeansL2CohM(c, v');
    }
  }

  lemma NoOpPreservesL2NotDirIMeansLoadableCoh(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2NotDirIMeansLoadableCoh(c, v)
    ensures L2NotDirIMeansLoadableCoh(c, v')
  {
    if step.TileStep? && step.tile_step.L2Step? {
      assert L2NotDirIMeansLoadableCoh(c, v');
    }
  }
  
  lemma NoOpPreservesPrivateMorphInL2IsCohM(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires PrivateMorphInL2IsCohM(c, v)
    ensures PrivateMorphInL2IsCohM(c, v')
  {}
  
  lemma NoOpPreservesEpochEntryInMorphWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EpochEntryInMorphWorkingSet(c, v)
    ensures EpochEntryInMorphWorkingSet(c, v')
  {}
  


  import opened OnMissInProgressPrivateProof
  import opened OnEvictInProgressPrivateProof
  import opened OnWritebackInProgressPrivateProof
  import opened OnMissInProgressSharedProof
  import opened OnEvictInProgressSharedProof
  import opened OnWritebackInProgressSharedProof
  import opened EngineBoundMsgUniqueCBProof
  import opened NetworkDiffCBsProof
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

  lemma NoOpPreservesInvPerfStore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvPerfStore(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesWF(c, v, v', step);
    NoOpPreservesCoreRuntimeDataMatchesWithGhostRuntimeData(c, v, v', step);
    NoOpPreservesRunningCallbackValuesAgree(c, v, v', step);
    NoOpPreservesUniqueTileForCallbackAddr(c, v, v', step);
    NoOpPreservesUniqueCurrentCallbacktoAddr(c, v, v', step);
    NoOpPreservesCurrentCallbackIsRunning(c, v, v', step);
  }

  lemma NoOpPreservesInvCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvCorrectCore(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesWF(c, v, v', step);
    NoOpPreservesEachAddrInEngineIsInCorrectCore(c, v, v', step);
    NoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
    NoOpPreservesEachAddrInCacheBoundMsgHasCorrectCore(c, v, v', step);
    NoOpPreservesL2PrivateMorphAddressesAreCorrectCore(c, v, v', step);
    NoOpPreservesL3MorphAddressesAreCorrectCore(c, v, v', step);
    NoOpPreservesL1PrivateMorphAddressesAreCorrectCore(c, v, v', step);
    NoOpPreservesEL1PrivateMorphAddressesAreCorrectCore(c, v, v', step);
    NoOpPreservesProxyPrivateMorphAddressesAreCorrectCore(c, v, v', step);
  }

  lemma NoOpPreservesInvAddressesUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvAddressesUnique(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesL1AddressesUnique(c, v, v', step);
    NoOpPreservesEL1AddressesUnique(c, v, v', step);
    NoOpPreservesProxyAddressesUnique(c, v, v', step);
    NoOpPreservesL2AddressesUnique(c, v, v', step);
    NoOpPreservesL3AddressesUnique(c, v, v', step);
  }

  lemma NoOpPreservesInvCallbackProgress_1(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
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
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesWF(c, v, v', step);
    NoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
    NoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
    NoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
    NoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
    NoOpPreservesExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v, v', step);
    NoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
    NoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
    NoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
  }

  lemma NoOpPreservesInvCallbackProgress_2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
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
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
    NoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
    NoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);

    NoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
    NoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
    NoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);

    NoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
    NoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
    NoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
  }

  lemma NoOpPreservesInvCallbackProgress_3(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
    ensures NoDupIdxsInCBOrderTracker(c, v')

    ensures EachAddrCacheBoundMsgIsUnique(c, v')
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step);
    NoOpPreservesNoDupIdxsInCBOrderTracker(c, v, v', step);

    NoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
    NoOpPreservesEachAddrCacheBoundMsgIsUnique(c, v, v', step);
  }

  lemma NoOpPreservesInvCallbackProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvCallbackProgress(c, v')
  {
    NoOpPreservesInvCallbackProgress_1(c, v, v');
    NoOpPreservesInvCallbackProgress_2(c, v, v');
    NoOpPreservesInvCallbackProgress_3(c, v, v');
  }

  lemma NoOpPreservesInvStartCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvStartCallback(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesWF(c, v, v', step);
    NoOpPreservesUnstartedBufferEntryWellformed(c, v, v', step);
    NoOpPreservesExistingCallbackIdsHaveCorrectEpoch(c, v, v', step);
    NoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
    NoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
    NoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
  }

  lemma NoOpPreservesInvEpochs(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvEpochs(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
    NoOpPreservesOnlyHeadOfCBOrderTrackerIsRunning(c, v, v', step);
    NoOpPreservesMorphWorkingSetInEpochs(c, v, v', step);
    NoOpPreservesEpochEntryInMorphWorkingSet(c, v, v', step);
    NoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
    NoOpPreservesPendingMemMeansNonMorphAddress(c, v, v', step);
    NoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
    NoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step);
  }


  lemma NoOpPreservesInvDirtyBit1(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
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
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesL2DirtyBitTracksInterveningWrite(c, v, v', step);
    NoOpPreservesL3DirtyBitTracksInterveningWrite(c, v, v', step);

    NoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
    NoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);

    NoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
    NoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
    NoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
    NoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);

    NoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
    NoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);

    NoOpPreservesDirtyMorphAddressMeansInterveningWriteCore(c, v, v', step);
    NoOpPreservesDirtyMorphAddressMeansInterveningWriteEngine(c, v, v', step);
    NoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);

    // NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v, v', step);
  }
  
  lemma NoOpPreservesInvDirtyBit2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
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
    var step :| Tako.NextStep(c, v, v', step, NoOp);

    NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v, v', step);
    NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v, v', step);
    NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
    NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);

    NoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
    NoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
    NoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
    NoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);

    NoOpPreservesPreMStateMeansNotDirtyCore(c, v, v', step);
    NoOpPreservesPreMStateMeansNotDirtyEngine(c, v, v', step);
    NoOpPreservesPreMStateMeansNotDirtyL2(c, v, v', step);

    NoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
    NoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
    NoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
    NoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
  }

  lemma NoOpPreservesInvDirtyBit(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvDirtyBit(c, v')
  {
    NoOpPreservesInvDirtyBit1(c, v, v');
    NoOpPreservesInvDirtyBit2(c, v, v');
  }

  lemma NoOpPreservesInvCoherenceState(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvCoherenceState(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
    NoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);

    assume {:axiom} L2DirISMatchesLastWrite(c, v');
    assume {:axiom} L3DirISMatchesLastWrite(c, v');
  
    assume {:axiom} CoreLoadableMatchesLastWriteMorph(c, v');
    assume {:axiom} EngineLoadableMatchesLastWriteMorph(c, v');

    assume {:axiom} CoreLoadableMatchesLastWriteRegular(c, v');
    assume {:axiom} EngineLoadableMatchesLastWriteRegular(c, v');

    NoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
    NoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
    NoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);

    NoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
    NoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
    NoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
    
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
  
    NoOpPreservesL2AddrNotInCacheMeansNoLoadableInCore(c, v, v', step);
    NoOpPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c, v, v', step);
    NoOpPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c, v, v', step);

    assume {:axiom} L3AddrNotInCacheMeansL2AddrNotInCache(c, v');
    assume {:axiom} L3DirectoryInIMeansL2AddrNotInCache(c, v');

    assume {:axiom} L1InCohMMeansAddrNotInOtherL1s(c, v');
    assume {:axiom} EL1InCohMMeansAddrNotInOtherL1s(c, v');
    assume {:axiom} L2InCohMMeansAddrNotInOtherL2s(c, v');

    assume {:axiom} L1InCohMMeansNoT1DataInFlight(c, v');
    assume {:axiom} EL1InCohMMeansNoT1DataInFlight(c, v');

    assume {:axiom} MInCoreMeansMinL2(c, v');
    assume {:axiom} MInEngineMeansMinL2(c, v');
    
    NoOpPreservesL2DirMorSDMeansL2CohM(c, v, v', step);
    NoOpPreservesL2NotDirIMeansLoadableCoh(c, v, v', step);
    NoOpPreservesPrivateMorphInL2IsCohM(c, v, v', step);
  }

  lemma NoOpPreservesInvWFMessages(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvWFMessages(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesWF(c, v, v', step);
    NoOpPreservesL2QueueHeadsWellformed(c, v, v', step);
    NoOpPreservesL3QueueHeadsWellformed(c, v, v', step);
    NoOpPreservesMemMessagesWellformed(c, v, v', step);

    NoOpPreservesL3DirOwnerIsAlwaysTier2Cache(c, v, v', step);
    NoOpPreservesL3DirSharersAlwaysTier2Cache(c, v, v', step);
    NoOpPreservesL2DirOwnerIsAlwaysTier1Cache(c, v, v', step);
    NoOpPreservesL2DirSharersAlwaysTier1Cache(c, v, v', step);

    NoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
    NoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
    NoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
    NoOpPreservesAllReqsToTier2HasTier1Source(c, v, v', step);
    NoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
    NoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
    NoOpPreservesAllDataToTier2FromCache(c, v, v', step);
    NoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
  }
  
  lemma NoOpPreservesInvCoherenceMessages(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvCoherenceMessages(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
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

  lemma NoOpPreservesInvPerfLoad(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures InvPerfLoad(c, v')
  {
    var step :| Tako.NextStep(c, v, v', step, NoOp);
    NoOpPreservesAddrInEpochMeansEventsWellformed(c, v, v', step);
    NoOpPreservesAddrInEpochMeansEventsMatchAddrAtomicity(c, v, v', step);
    NoOpPreservesWritesToAddrWellFormed(c, v, v', step);
    NoOpPreservesAllWritesInWritesToAddr(c, v, v', step);
    NoOpPreservesMoDeterminedByWritesToAddrOrder(c, v, v', step);
    NoOpPreservesAllMoInWritesToAddr(c, v, v', step);
    NoOpPreservesAllWritesToAddrLessThanCurrentPCCore(c, v, v', step);
    NoOpPreservesAllWritesToAddrLessThanCurrentPCEngine(c, v, v', step);
    NoOpPreservesWritesToAddrHaveValidThreadIds(c, v, v', step);
  }



  lemma NoOpPreservesInv(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables)
    requires Tako.Next(c, v, v', NoOp)
    requires TakoRefinementDefns.Inv(c, v)
    ensures TakoRefinementDefns.Inv(c, v')
  {
    NoOpPreservesInvPerfStore(c, v, v');
    NoOpPreservesInvCorrectCore(c, v, v');
    NoOpPreservesInvAddressesUnique(c, v, v');
    NoOpPreservesInvCallbackProgress(c, v, v');
    NoOpPreservesInvStartCallback(c, v, v');
    NoOpPreservesInvEpochs(c, v, v');
    NoOpPreservesInvDirtyBit(c, v, v');
    NoOpPreservesInvWFMessages(c, v, v');
    NoOpPreservesInvCoherenceState(c, v, v');
    NoOpPreservesInvCoherenceMessages(c, v, v');
    NoOpPreservesInvPerfLoad(c, v, v');
  }
}