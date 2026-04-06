include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnMissInProgressPrivateProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  ///////////////////////////////////////////////////////////////////////////////////
  // OnMissInProgressIffCacheEntryPendingPrivate
  ///////////////////////////////////////////////////////////////////////////////////
  // TODO: slow
  lemma CoreCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetSStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma CoreCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetMStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma CoreCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.RecvMsgStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma CoreCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.EvictStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma CoreNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    if step.tile_step.core_step.CacheCommunicationStep? {
      match step.tile_step.core_step.step {
        case GetSStep() => CoreCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
        case GetMStep() => CoreCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
        case RecvMsgStep() => CoreCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
        case EvictStep() => CoreCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
    } else {
      assert false;
    }
  }

  lemma CoreNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma CoreNoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    CoreNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
    CoreNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
  }


  lemma MemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }


  lemma MemoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma MemoryNoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    MemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
    MemoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
  }


  lemma ProxyCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires step.tile_step.proxy_step.step.GetMStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma ProxyCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires step.tile_step.proxy_step.step.GetSStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma ProxyCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires step.tile_step.proxy_step.step.EvictStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma ProxyCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires step.tile_step.proxy_step.step.RecvMsgStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma ProxyNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    assert step.tile_step.proxy_step.CacheCommunicationStep?;
    match step.tile_step.proxy_step.step {
      case GetSStep() => ProxyCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      case GetMStep() => ProxyCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      case RecvMsgStep() => ProxyCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      case EvictStep() => ProxyCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
    }
  }

  lemma ProxyNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma ProxyNoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    ProxyNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
    ProxyNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
  }

  lemma L2CacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.GetSStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L2CacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.GetMStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L2CacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.EvictStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L2CacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.RecvMsgStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L2DirectoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L2DirectoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        if step.tile_step.l2_step.eng_req.OnMiss?
        && c_idx == step.tile_step.l2_step.eng_req.idx
        && addr == step.tile_step.l2_step.addr
        {
          // assert addr == step.tile_step.l2_step.addr;
          assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
        } else {
          var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
          assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
          assert InFlightOnMissRequest(c, v, addr, c_idx);
          assert OnMissInProgress(c, v, addr, c_idx);
          assert L2PendingCallbackForAddr(c, v, addr, c_idx);
        }
        assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
        assert L2PendingCallbackForAddr(c, v, addr, c_idx);
        assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
        assert L2PendingCallbackForAddr(c, v, addr, c_idx);
        assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      if L2PendingCallbackForAddr(c, v, addr, c_idx) {
        assert OnMissInProgress(c, v, addr, c_idx);
        if InFlightOnMissRequest(c, v, addr, c_idx) {
          reveal InFlightOnMissRequest;
          var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
          assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
          assert InFlightOnMissRequest(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
            && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
          assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
          assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
          assert OnMissInProgress(c, v', addr, c_idx);
        } else {
          reveal InFlightOnMissResponse;
          var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
          assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
          assert InFlightOnMissResponse(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        }
      } else {
        assert !L2PendingCallbackForAddr(c, v, addr, c_idx);
        reveal L2PendingCallbackForAddr;
        assert c_idx == step.tile_step.l2_step.eng_req.idx;
        assert addr == step.tile_step.l2_step.addr;
        var idx := if addr in v.network.inFlightEngReqs then |v.network.inFlightEngReqs[addr]| else 0;
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx) by { reveal InFlightOnMissRequest; }
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      if step.tile_step.l2_step.eng_resp.idx == c_idx && v.tiles[step.tile_idx].l2.cache[c_idx].addr == addr {
        assert IsInFlightOnMissResponse(c, v, addr, step.msgOps.recv.val, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
        assert !InFlightOnMissResponse(c, v', addr, c_idx) by {
          reveal InFlightOnMissResponse;
          if InFlightOnMissResponse(c, v', addr, c_idx) {
            var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
            assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
            assert msg == step.msgOps.recv.val;
            assert !IsInFlightOnMissResponse(c, v', addr, step.msgOps.recv.val, c_idx);
            assert false;
          }
        }
        assert !CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert !CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
        assert !InFlightOnMissRequest(c, v', addr, c_idx) by { reveal InFlightOnMissRequest; }
        assert !OnMissInProgress(c, v', addr, c_idx);
        assert false;
      } else {
        assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        if IsInFlightOnMissResponse(c, v', addr, msg, c_idx) {
          assert InFlightOnMissResponse(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        } else {
          assert msg == step.msgOps.recv.val;
          reveal L2PendingCallbackForAddr;
          assert !L2PendingCallbackForAddr(c, v', addr, c_idx);
          assert false;
        }
      }
    }
  }

  lemma L2NoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    match step.tile_step.l2_step {
      case CacheCommunicationStep(c_step, _, _, _) => {
        match c_step {
          case EvictStep() => {
            L2CacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case RecvMsgStep() => {
            L2CacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case GetSStep() => {
            L2CacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case GetMStep() => {
            L2CacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
        }
        L2CacheCommunicationNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case DirectoryStep(_, _, _) => {
        L2DirectoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
        L2DirectoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case ScheduleCallbackStep(_, _, _) => {
        L2ScheduleCallbackNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
        L2ScheduleCallbackNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case ReceiveOnMissDataStep(_) => {
        L2ReceiveOnMissDataNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
        L2ReceiveOnMissDataNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case ReceiveCoherenceMessageStep() => {
        L2ReceiveCoherenceMessageNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
        L2ReceiveCoherenceMessageNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
    }
  }

  lemma L3DirectoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L3ReqMemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L3RespMemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma L3NoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L3NoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    match step.tile_step.l3_step {
      case DirectoryStep(_, _, _) => {
        L3DirectoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case ScheduleCallbackStep(_, _, _) => {
        L3ScheduleCallbackNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case ReceiveOnMissDataStep(_) => {
        L3ReceiveOnMissDataNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case ReqMemoryStep(_,_) => {
        L3ReqMemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case RespMemoryStep(_) => {
        L3RespMemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case ReceiveCoherenceMessageStep() => {
        L3ReceiveCoherenceMessageNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
    }
    L3NoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
  }

  lemma EngineReceiveCallbackReqNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        var new_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
        assert IsInFlightOnMissRequest(c, v, addr, new_idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx) {
          assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
          assert OnMissInProgress(c, v, addr, c_idx);
        } else {
          assert addr == step.msgOps.recv.val.meta.addr;
          assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
          assert InFlightOnMissRequest(c, v, addr, c_idx) by { reveal InFlightOnMissRequest; }
          assert OnMissInProgress(c, v, addr, c_idx);
        }
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma EngineCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetSStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma EngineCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetMStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma EngineCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.EvictStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma EngineCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma EngineNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    match step.tile_step.eng_step {
      case CacheCommunicationStep(c_step, _, _, _) => {
        match c_step {
          case GetSStep() => {
            EngineCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case GetMStep() => {
            EngineCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case EvictStep() => {
            EngineCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case RecvMsgStep() => {
            EngineCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
        }
      }
      case ReceiveCallbackReqStep(_) => {
        EngineReceiveCallbackReqNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case _ => {
        assert false;
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx: nat :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        if IsInFlightOnMissRequest(c, v', addr, idx, c_idx) {
          assert InFlightOnMissRequest(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        } else if idx > 0 && IsInFlightOnMissRequest(c, v', addr, idx - 1, c_idx) {
          assert InFlightOnMissRequest(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        } else {
          // received, so now callback will be present
          // assert !IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
          assert idx == 0;
          assert step.msgOps.recv.val.engine_req.OnMiss?;
          assert step.msgOps.recv.val.engine_req == EngineRequest.OnMiss(c_idx);
          assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          // && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
          assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
          assert OnMissInProgress(c, v', addr, c_idx);
        }
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma EngineNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    if step.tile_step.eng_step.ReceiveCallbackReqStep? {
      EngineReceiveCallbackReqNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
    } else {
      EngineNotReceiveCallbackReqNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
    }
  }

  lemma EngineNoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    EngineNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
    EngineNoOpPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
  }

  lemma NoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        MemoryNoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step);
          }
        }
      }
    }
  }

  ///////////////////////////////////////////////////////////////////
  // Perform Inst Cases
  ///////////////////////////////////////////////////////////////////
  lemma PerformNextInstFwdPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma PerformNextInstRevPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma PerformNextInstPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    PerformNextInstFwdPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step, re);
    PerformNextInstRevPreservesOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step, re);
  }


  ///////////////////////////////////////////////////////////////////
  // Start/End CB Cases
  ///////////////////////////////////////////////////////////////////
  lemma StartCBPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma StartCBPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }


  lemma StartCBPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    StartCBPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step, re);
    StartCBPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step, re);
  }

  lemma EndCBPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L2PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        if IsInFlightOnMissResponse(c, v, addr, msg, c_idx) {
          assert InFlightOnMissResponse(c, v, addr, c_idx);
          assert OnMissInProgress(c, v, addr, c_idx);
        } else {
          assert msg in step.msgOps.send;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
          assert OnMissInProgress(c, v, addr, c_idx);
        }
      }
      assert L2PendingCallbackForAddr(c, v, addr, c_idx);
      assert L2PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L2PendingCallbackForAddr; }
    }
  }

  lemma EndCBPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L2PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L2PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx) {
          assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
          assert OnMissInProgress(c, v', addr, c_idx);
        } else {
          // this entry finished, so response should exist
          var msg :| msg in step.msgOps.send;
          assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
          assert InFlightOnMissResponse(c, v', addr, c_idx) by { reveal InFlightOnMissResponse; }
          assert OnMissInProgress(c, v', addr, c_idx);
        }
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }


  lemma EndCBPreservesOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissInProgressIffCacheEntryPendingPrivate(c, v')
  {
    EndCBPreservesFwdOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step, re);
    EndCBPreservesRevOnMissInProgressIffCacheEntryPendingPrivate(c, v, v', step, re);
  }
}