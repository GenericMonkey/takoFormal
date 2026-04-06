include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnWritebackInProgressLoadableProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) && v'.tiles[core].core.cache[idx].addr.Morph? by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
      if core == step.tile_idx
        && idx == step.tile_step.core_step.idx
        && step.tile_step.core_step.step.RecvMsgStep?
        && step.msgOps.recv.val.coh_msg.Data?
      {
        var addr := v'.tiles[core].core.cache[idx].addr;
        assert DataInFlight(c, v, addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, L1), step.msgOps.recv.val.coh_msg.val) by {
          reveal DataInFlight;
        }
        var dir_idx: nat :| NonEmptyNonPendingL2CacheEntry(c, v, core, dir_idx)
          && v.tiles[core].l2.cache[dir_idx].addr == addr
          && v.tiles[core].l2.cache[dir_idx].coh.Loadable();
        if SharedMorph(addr) {
          assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
          assert L2AddrNotInCache(c, v, core, addr); // not loadable okay?
        }
        assert false;
      }
    }
  }

  lemma MemoryNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma ProxyNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          var new_idx := if step.msgOps.recv.val.meta.addr == v'.tiles[core].core.cache[idx].addr then req_idx + 1 else req_idx;
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, new_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          if tile == step.tile_idx && buf == step.tile_step.eng_step.idx {
            assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, 0, val);
            assert InFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, val) by { reveal InFlightOnWritebackRequest; }
            assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
          } else {
            assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
            assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
          }
        }
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }
  
  lemma L2DirectoryNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }
  
  lemma L2CacheCommunicationNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
        reveal InFlightOnWritebackRequest;
        var msg :| msg in step.msgOps.send;
        if msg.meta.addr == v'.tiles[core].core.cache[idx].addr {
          if msg.engine_req.OnMiss? {
            assert PrivateMorph(msg.meta.addr);
            assert step.tile_idx == msg.meta.addr.morphType.idx;
            if NonEmptyL1CacheEntry(c, v, core, idx) {
              assert core == step.tile_idx;
            } else {
              assert v.tiles[core].core.cache[idx].coh.I?;
            }
            assert L2AddrNotInCache(c, v, step.tile_idx, v'.tiles[core].core.cache[idx].addr);
          } else {
            assert DirIL2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.idx);
          }
        } else {
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
        reveal InFlightOnWritebackRequest;
        var msg :| msg in step.msgOps.send;
        if msg.meta.addr == v'.tiles[core].core.cache[idx].addr {
          if msg.engine_req.OnMiss? {
            assert step.tile_idx == c.addr_map(v'.tiles[core].core.cache[idx].addr);
            assert L3AddrNotInCache(c, v, step.tile_idx, v'.tiles[core].core.cache[idx].addr);
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].core.cache[idx].addr);
          } else {
            assert DirIL3CacheEntry(c, v, step.tile_idx, step.tile_step.l3_step.idx);
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].core.cache[idx].addr);
          }
        } else {
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
      }
    }
  }

  lemma NoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)

    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)

    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
              }
              case CacheCommunicationStep(_, _, _, _) => {
                L2CacheCommunicationNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
              }
              case DirectoryStep(_, _, _) => {
                L2DirectoryNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
              }
              case ScheduleCallbackStep(_, _, _) => {
                L2ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                  L2ReceiveOnMissDataNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            if l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInCore(c, v, v', step);
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma StartEndCBPreservesOnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma CoreNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma MemoryNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma ProxyNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert step.tile_step.eng_step.CacheCommunicationStep?;
      assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val)  && v'.tiles[core].engine.cache[idx].addr.Morph? by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
      if core == step.tile_idx
        && idx == step.tile_step.eng_step.c_idx
        && step.tile_step.eng_step.step.RecvMsgStep?
        && step.msgOps.recv.val.coh_msg.Data?
      {
        var addr := v'.tiles[core].engine.cache[idx].addr;
        assert DataInFlight(c, v, addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, eL1), step.msgOps.recv.val.coh_msg.val) by {
          reveal DataInFlight;
        }
        var dir_idx: nat :| NonEmptyNonPendingL2CacheEntry(c, v, core, dir_idx)
          && v.tiles[core].l2.cache[dir_idx].addr == addr
          && v.tiles[core].l2.cache[dir_idx].coh.Loadable();
        if SharedMorph(addr) {
          assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
          assert L2AddrNotInCache(c, v, core, addr); // not loadable okay?
        }
        assert false;
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          var new_idx := if step.msgOps.recv.val.meta.addr == v'.tiles[core].engine.cache[idx].addr then req_idx + 1 else req_idx;
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, new_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          if tile == step.tile_idx && buf == step.tile_step.eng_step.idx {
            assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, 0, val);
            assert InFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, val) by { reveal InFlightOnWritebackRequest; }
            assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
          } else {
            assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
            assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
          }
        }
      }
    }
  }

  lemma L2NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires !step.tile_step.l2_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
        reveal InFlightOnWritebackRequest;
        var msg :| msg in step.msgOps.send;
        if msg.meta.addr == v'.tiles[core].engine.cache[idx].addr {
          if msg.engine_req.OnMiss? {
            assert PrivateMorph(msg.meta.addr);
            assert step.tile_idx == msg.meta.addr.morphType.idx;
            if NonEmptyEL1CacheEntry(c, v, core, idx) {
              assert core == step.tile_idx;
            } else {
              assert v.tiles[core].engine.cache[idx].coh.I?;
            }
            assert L2AddrNotInCache(c, v, step.tile_idx, v'.tiles[core].engine.cache[idx].addr);
          } else {
            assert DirIL2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.idx);
          }
        } else {
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
        reveal InFlightOnWritebackRequest;
        var msg :| msg in step.msgOps.send;
        if msg.meta.addr == v'.tiles[core].engine.cache[idx].addr {
          if msg.engine_req.OnMiss? {
            assert L3AddrNotInCache(c, v, step.tile_idx, v'.tiles[core].engine.cache[idx].addr);
            assert step.tile_idx == c.addr_map(v'.tiles[core].engine.cache[idx].addr);
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].engine.cache[idx].addr);
          } else {
            assert DirIL3CacheEntry(c, v, step.tile_idx, step.tile_step.l3_step.idx);
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].engine.cache[idx].addr);
          }
        } else {
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
      }
    }
  }

  lemma NoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)

    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)

    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
          }
          case L2Step(l2_step) => {
            if l2_step.ScheduleCallbackStep? {
              L2ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
            } else {
              L2NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
            }
          }
          case L3Step(l3_step) => {
            if l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInEngine(c, v, v', step);
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma StartEndCBPreservesOnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma CoreNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    assert step.tile_step.core_step.CacheCommunicationStep?;
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma MemoryNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma EngineCacheCommunicationNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma ProxyNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert step.tile_step.proxy_step.CacheCommunicationStep?;
      assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) && v'.tiles[core].proxy.cache[idx].addr.Morph? by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) && v'.tiles[core].proxy.cache[idx].addr.Morph? by {
            reveal InFlightOnWritebackRequest;
            var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
            assert InFlightEngineRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx);
            assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          }
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) && v'.tiles[core].proxy.cache[idx].addr.Morph? by {
            reveal CallbackPresent;
            var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
            assert IsBufferEntry(c, v, tile, buf);
            assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          }
        }
      }
      if core == step.tile_idx
        && idx == step.tile_step.proxy_step.idx
        && step.tile_step.proxy_step.step.RecvMsgStep?
        && step.msgOps.recv.val.coh_msg.Data?
      {
        var addr := v'.tiles[core].proxy.cache[idx].addr;
          assert DataInFlight(c, v, addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, Proxy), step.msgOps.recv.val.coh_msg.val) by {
            reveal DataInFlight;
          }
        var dir_idx: nat :| NonEmptyNonPendingL2CacheEntry(c, v, core, dir_idx)
          && v.tiles[core].l2.cache[dir_idx].addr == addr
          && v.tiles[core].l2.cache[dir_idx].coh.Loadable();
        if SharedMorph(addr) {
          assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
          assert L2AddrNotInCache(c, v, core, addr); // not loadable okay?
        }
        assert false;
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          var new_idx := if step.msgOps.recv.val.meta.addr == v'.tiles[core].proxy.cache[idx].addr then req_idx + 1 else req_idx;
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, new_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          if tile == step.tile_idx && buf == step.tile_step.eng_step.idx {
            assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, 0, val);
            assert InFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by { reveal InFlightOnWritebackRequest; }
            assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
          } else {
            assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
            assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
          }
        }
      }
    }
  }

  lemma L2NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires !step.tile_step.l2_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires ProxyPrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
        reveal InFlightOnWritebackRequest;
        var msg :| msg in step.msgOps.send;
        if msg.meta.addr == v'.tiles[core].proxy.cache[idx].addr {
          if msg.engine_req.OnMiss? {
            assert PrivateMorph(msg.meta.addr);
            assert step.tile_idx == msg.meta.addr.morphType.idx;
            if NonEmptyProxyCacheEntry(c, v, core, idx) {
              assert core == step.tile_idx;
            } else {
              assert v.tiles[core].proxy.cache[idx].coh.I?;
            }
            assert L2AddrNotInCache(c, v, step.tile_idx, v'.tiles[core].proxy.cache[idx].addr);
          } else {
            assert DirIL2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.idx);
          }
        } else {
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
        reveal InFlightOnWritebackRequest;
        var msg :| msg in step.msgOps.send;
        if msg.meta.addr == v'.tiles[core].proxy.cache[idx].addr {
          if msg.engine_req.OnMiss? {
            assert L3AddrNotInCache(c, v, step.tile_idx, v'.tiles[core].proxy.cache[idx].addr);
            assert step.tile_idx == c.addr_map(v'.tiles[core].proxy.cache[idx].addr);
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].proxy.cache[idx].addr);
          } else {
            assert DirIL3CacheEntry(c, v, step.tile_idx, step.tile_step.l3_step.idx);
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].proxy.cache[idx].addr);
          }
        } else {
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
      }
    }
  }

  lemma NoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    requires ProxyPrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)

    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)

    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
          }
          case L2Step(l2_step) => {
            if l2_step.ScheduleCallbackStep? {
              L2ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
            } else {
              L2NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
            }
          }
          case L3Step(l3_step) => {
            if l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
            } else {
              EngineCacheCommunicationNoOpPreservesOnWritebackInProgressMeansNoLoadableInProxy(c, v, v', step);
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }

  lemma StartEndCBPreservesOnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    ensures OnWritebackInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnWritebackInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnWritebackRequest;
          var req_idx :| IsInFlightOnWritebackRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnWritebackRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnWriteBack, tile, buf);
        }
      }
    }
  }
}