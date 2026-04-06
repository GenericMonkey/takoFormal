include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnEvictInProgressLoadableProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) && v'.tiles[core].core.cache[idx].addr.Morph? by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
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

  lemma MemoryNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma ProxyNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          var new_idx := if step.msgOps.recv.val.meta.addr == v'.tiles[core].core.cache[idx].addr then req_idx + 1 else req_idx;
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, new_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          if tile == step.tile_idx && buf == step.tile_step.eng_step.idx {
            assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, 0, val);
            assert InFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, val) by { reveal InFlightOnEvictRequest; }
            assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
          } else {
            assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
            assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
          }
        }
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }
  
  lemma L2DirectoryNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }
  
  lemma L2ReceiveOnMissDataNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
        reveal InFlightOnEvictRequest;
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
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
        reveal InFlightOnEvictRequest;
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
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val);
      }
    }
  }

  lemma NoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)

    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)

    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
              }
              case CacheCommunicationStep(_, _, _, _) => {
                L2CacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
              }
              case DirectoryStep(_, _, _) => {
                L2DirectoryNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
              }
              case ScheduleCallbackStep(_, _, _) => {
                L2ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                  L2ReceiveOnMissDataNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            if l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesOnEvictInProgressMeansNoLoadableInCore(c, v, v', step);
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma StartCBPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma EndCBPreservesOnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].core.cache[idx].addr, val)
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].core.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].core.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].core.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].core.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].core.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma CoreNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    assert step.tile_step.core_step.CacheCommunicationStep?;
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma MemoryNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma ProxyNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma EngineCacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert step.tile_step.eng_step.CacheCommunicationStep?;
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) && v'.tiles[core].engine.cache[idx].addr.Morph? by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
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
        if PrivateMorph(addr) {
          assert false;
        } else {
          assert SharedMorph(addr);
          assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
          assert L2AddrNotInCache(c, v, core, addr); // not loadable okay?
          assert false;
        }
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          var new_idx := if step.msgOps.recv.val.meta.addr == v'.tiles[core].engine.cache[idx].addr then req_idx + 1 else req_idx;
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, new_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          if tile == step.tile_idx && buf == step.tile_step.eng_step.idx {
            assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, 0, val);
            assert InFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, val) by { reveal InFlightOnEvictRequest; }
            assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
          } else {
            assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
            assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
          }
        }
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }
  lemma L2DirectoryNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }
  lemma L2CacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
        reveal InFlightOnEvictRequest;
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
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
        reveal InFlightOnEvictRequest;
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
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val);
      }
    }
  }

  lemma NoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)

    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)

    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            if l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
            } else {
              EngineCacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInEngine(c, v, v', step);
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma StartEndCBPreservesOnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures OnEvictInProgressMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].engine.cache[idx].addr, val)
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].engine.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].engine.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].engine.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].engine.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].engine.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }
  
  lemma CoreNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    assert step.tile_step.core_step.CacheCommunicationStep?;
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma MemoryNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma EngineCacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma ProxyNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert step.tile_step.proxy_step.CacheCommunicationStep?;
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) && v'.tiles[core].proxy.cache[idx].addr.Morph? by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) && v'.tiles[core].proxy.cache[idx].addr.Morph? by {
            reveal InFlightOnEvictRequest;
            var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
            assert InFlightEngineRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx);
            assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          }
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) && v'.tiles[core].proxy.cache[idx].addr.Morph? by {
            reveal CallbackPresent;
            var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
            assert IsBufferEntry(c, v, tile, buf);
            assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          }
        }
        assert v'.tiles[core].proxy.cache[idx].addr.Morph?;
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

  lemma EngineReceiveCallbackReqNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          var new_idx := if step.msgOps.recv.val.meta.addr == v'.tiles[core].proxy.cache[idx].addr then req_idx + 1 else req_idx;
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, new_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          if tile == step.tile_idx && buf == step.tile_step.eng_step.idx {
            assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, 0, val);
            assert InFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by { reveal InFlightOnEvictRequest; }
            assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
          } else {
            assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
            assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
          }
        }
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L2DirectoryNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires ProxyPrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
        reveal InFlightOnEvictRequest;
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
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
        reveal InFlightOnEvictRequest;
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
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
        }
      } else {
        assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val);
      }
    }
  }

  lemma NoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    requires ProxyPrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)

    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)

    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            if l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
            } else {
              EngineCacheCommunicationNoOpPreservesOnEvictInProgressMeansNoLoadableInProxy(c, v, v', step);
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }

  lemma StartEndCBPreservesOnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    ensures OnEvictInProgressMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v', v'.tiles[core].proxy.cache[idx].addr, val)
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert OnEvictInProgress(c, v, v'.tiles[core].proxy.cache[idx].addr, val) by {
        if InFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, val) {
          reveal InFlightOnEvictRequest;
          var req_idx :| IsInFlightOnEvictRequest(c, v', v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
          assert IsInFlightOnEvictRequest(c, v, v'.tiles[core].proxy.cache[idx].addr, req_idx, val);
        } else {
          assert CallbackPresent(c, v', v'.tiles[core].proxy.cache[idx].addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].proxy.cache[idx].addr, CallbackType.OnEvict, tile, buf);
        }
      }
    }
  }
}