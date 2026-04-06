include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OutEpochDefnProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma ProxyNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma MemoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma EngineCacheCommunicationNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              if idx == 0 && step.tile_step.eng_step.ReceiveCallbackReqStep? && step.msgOps.recv.val.meta.addr == addr {
                assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
                assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val)) by { reveal CallbackPresent; }
                assert OnEvictInProgress(c, v', addr, val);
                assert false;
              } else {
                var new_idx := (if (
                  && step.tile_step.eng_step.ReceiveCallbackReqStep?
                  && step.msgOps.recv.val.meta.addr == addr
                ) then
                  idx - 1
                else
                  idx
                );
                assert IsInFlightOnEvictRequest(c, v', addr, new_idx, val);
                assert OnEvictInProgress(c, v', addr, val);
                assert false;
              }
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              if idx == 0 && step.tile_step.eng_step.ReceiveCallbackReqStep? && step.msgOps.recv.val.meta.addr == addr {
                assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
                assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val)) by { reveal CallbackPresent; }
                assert OnWritebackInProgress(c, v', addr, val);
                assert false;
              } else {
                var new_idx := (if (
                  && step.tile_step.eng_step.ReceiveCallbackReqStep?
                  && step.msgOps.recv.val.meta.addr == addr
                ) then
                  idx - 1
                else
                  idx
                );
                assert IsInFlightOnWritebackRequest(c, v', addr, new_idx, val);
                assert OnWritebackInProgress(c, v', addr, val);
                assert false;
              }
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              var new_idx := (if (
                && step.tile_step.eng_step.ReceiveCallbackReqStep?
                && step.msgOps.recv.val.meta.addr == addr
              ) then
                req_idx + 1
              else
                req_idx
              );
              assert IsInFlightOnMissRequest(c, v, addr, new_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              if tile == step.tile_idx && buf == step.tile_step.eng_step.idx {
                assert IsInFlightOnMissRequest(c, v, addr, 0, idx);
                assert InFlightOnMissRequest(c, v, addr, idx) by {
                  reveal InFlightOnMissRequest;
                }
              } else {
                assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
                assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
              }
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              var new_idx := (if (
                && step.tile_step.eng_step.ReceiveCallbackReqStep?
                && step.msgOps.recv.val.meta.addr == addr
              ) then
                req_idx + 1
              else
                req_idx
              );
              assert IsInFlightOnMissRequest(c, v, addr, new_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              if tile == step.tile_idx && buf == step.tile_step.eng_step.idx {
                assert IsInFlightOnMissRequest(c, v, addr, 0, idx);
                assert InFlightOnMissRequest(c, v, addr, idx) by {
                  reveal InFlightOnMissRequest;
                }
              } else {
                assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
                assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L2DirectoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[addr.morphType.idx].l2.cache[idx].addr == addr {
            assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[addr.morphType.idx].l2.cache[idx].addr == addr {
            assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L2CacheCommunicationNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[addr.morphType.idx].l2.cache[idx].addr == addr {
            assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[addr.morphType.idx].l2.cache[idx].addr == addr {
            assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[addr.morphType.idx].l2.cache[idx].addr == addr {
            if NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) {
              assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?; 
              if InFlightOnMissRequest(c, v', addr, idx) {
                reveal InFlightOnMissRequest;
                var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
                assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
                assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
              } else {
                assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                  && !v'.tiles[tile].engine.buffer[buf].started;
                assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
                assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
              }
            } else {
              var req_idx := if addr in v.network.inFlightEngReqs then |v.network.inFlightEngReqs[addr]| else 0;
              var val := v.tiles[addr.morphType.idx].l2.cache[idx].dir.val;
              assert IsInFlightOnEvictRequest(c, v', addr, req_idx, val) || IsInFlightOnWritebackRequest(c, v', addr, req_idx, val);
              assert InFlightOnEvictRequest(c, v', addr, val) || InFlightOnWritebackRequest(c, v', addr, val) by {
                reveal InFlightOnEvictRequest;
                reveal InFlightOnWritebackRequest;
              }
              assert OnEvictInProgress(c, v', addr, val) || OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr {
            assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L3ReqMemoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr {
            assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L3RespMemoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    requires PendingMemMeansNonMorphAddress(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr {
            assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L3DirectoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr {
            assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr {
            assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
  
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          if v.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr {
            if NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) {
              assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?;
              if InFlightOnMissRequest(c, v', addr, idx) {
                reveal InFlightOnMissRequest;
                var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
                assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
                assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
              } else {
                assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                  && !v'.tiles[tile].engine.buffer[buf].started;
                assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
                assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
              }
            } else {
              var req_idx := if addr in v.network.inFlightEngReqs then |v.network.inFlightEngReqs[addr]| else 0;
              var val := v.tiles[c.addr_map(addr)].l3.cache[idx].dir.val;
              assert IsInFlightOnEvictRequest(c, v', addr, req_idx, val) || IsInFlightOnWritebackRequest(c, v', addr, req_idx, val);
              assert InFlightOnEvictRequest(c, v', addr, val) || InFlightOnWritebackRequest(c, v', addr, val) by {
                reveal InFlightOnEvictRequest;
                reveal InFlightOnWritebackRequest;
              }
              assert OnEvictInProgress(c, v', addr, val) || OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }


  lemma NoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    requires PendingMemMeansNonMorphAddress(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
              }
            }
          }
          case EngineStep(eng_step) => {
            if eng_step.CacheCommunicationStep? {
              EngineCacheCommunicationNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
            } else {
              assert eng_step.ReceiveCallbackReqStep?;
              EngineReceiveCallbackReqNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      forall val : Value
        ensures !OnEvictInProgress(c, v, addr, val)
        ensures !OnWritebackInProgress(c, v, addr, val)
      {
        assert !OnEvictInProgress(c, v, addr, val) by {
          assert !InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
              assert OnEvictInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
        assert !OnWritebackInProgress(c, v, addr, val) by {
          assert !InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
          assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
            reveal CallbackPresent;
            if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
              assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
              assert OnWritebackInProgress(c, v', addr, val);
              assert false;
            }
          }
        }
      }
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
          ensures (
            || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
          assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
          if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
            assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
          } else {
            assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
            if InFlightOnMissRequest(c, v', addr, idx) {
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
          ensures (
            || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
            || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
          )
        {
          assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
          assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
          if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
            assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
          } else {
            assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
            if InFlightOnMissRequest(c, v', addr, idx) { 
              reveal InFlightOnMissRequest;
              var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
              assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
            } else {
              assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
              reveal UnstartedCallbackPresent;
              var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                && !v'.tiles[tile].engine.buffer[buf].started;
              assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
              assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].Out?;
    }
  }

  lemma StartCBPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      if addr != entry.addr {
        forall val : Value
          ensures !OnEvictInProgress(c, v, addr, val)
          ensures !OnWritebackInProgress(c, v, addr, val)
        {
          assert !OnEvictInProgress(c, v, addr, val) by {
            assert !InFlightOnEvictRequest(c, v, addr, val) by {
              reveal InFlightOnEvictRequest;
              if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
                assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert OnEvictInProgress(c, v', addr, val);
                assert false;
              }
            }
            assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
              reveal CallbackPresent;
              if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
                assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
                assert OnEvictInProgress(c, v', addr, val);
                assert false;
              }
            }
          }
          assert !OnWritebackInProgress(c, v, addr, val) by {
            assert !InFlightOnWritebackRequest(c, v, addr, val) by {
              reveal InFlightOnWritebackRequest;
              if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
                assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert OnWritebackInProgress(c, v', addr, val);
                assert false;
              }
            }
            assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
              reveal CallbackPresent;
              if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
                assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
                assert OnWritebackInProgress(c, v', addr, val);
                assert false;
              }
            }
          }
        }
        if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
          forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
            ensures (
              || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
              || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
              || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
            )
          {
            assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
            assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
            if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
              assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
            } else {
              assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
              if InFlightOnMissRequest(c, v', addr, idx) {
                reveal InFlightOnMissRequest;
                var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
                assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
                assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
              } else {
                assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                  && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                  && !v'.tiles[tile].engine.buffer[buf].started;
                assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
                assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
              }
            }
          }
        }
        if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
          forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
            ensures (
              || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
              || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
              || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
            )
          {
            assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
            assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
            if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
              assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
            } else {
              assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
              if InFlightOnMissRequest(c, v', addr, idx) { 
                reveal InFlightOnMissRequest;
                var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
                assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
                assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
              } else {
                assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                  && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                  && !v'.tiles[tile].engine.buffer[buf].started;
                assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
                assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
              }
            }
          }
        }
        assert v.g.callback_epochs[addr].Out?;
      } else {
        // in this state, no callback should be startable for this addr
        if entry.cb_type.OnEvict? {
          assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          assert CallbackPresent(c, v', addr, entry.cb_type) by { reveal CallbackPresent; }
          assert OnEvictInProgress(c, v', addr, entry.cb_type.val);
          assert false;
        } else if entry.cb_type.OnWriteBack? {
          assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          assert CallbackPresent(c, v', addr, entry.cb_type) by { reveal CallbackPresent; }
          assert OnWritebackInProgress(c, v', addr, entry.cb_type.val);
          assert false;
        } else {
          assert entry.cb_type.OnMiss?;
          assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          assert CallbackPresent(c, v', addr, entry.cb_type) by { reveal CallbackPresent; }
          assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
          assert OnMissInProgress(c, v, addr, entry.cb_type.idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert InFlightOnMissRequest(c, v', addr, entry.cb_type.idx) || UnstartedCallbackPresent(c, v', addr, entry.cb_type);
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert InFlightOnMissRequest(c, v', addr, entry.cb_type.idx) || UnstartedCallbackPresent(c, v', addr, entry.cb_type);
          }
          if InFlightOnMissRequest(c, v', addr, entry.cb_type.idx) {
            reveal InFlightOnMissRequest;
            var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, entry.cb_type.idx);
            assert IsInFlightOnMissRequest(c, v, addr, req_idx, entry.cb_type.idx);
            assert InFlightOnMissRequest(c, v, addr, entry.cb_type.idx);
            assert false;
          } else {
            assert UnstartedCallbackPresent(c, v', addr, entry.cb_type);
            reveal UnstartedCallbackPresent;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
              && v'.tiles[tile].engine.buffer[buf].cb_type == entry.cb_type
              && !v'.tiles[tile].engine.buffer[buf].started;
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
            assert false;
          }
        }
      }
    }
  }

  lemma EndCBPreservesNoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    ensures NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v', addr, val))
      && (forall val :: !OnWritebackInProgress(c, v', addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx) :: (
          || v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==>
        (forall idx: nat | NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx) :: (
          || v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v', addr, idx))
          || (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx)))
        ))
      )
    )
      ensures v'.g.callback_epochs[addr].Out?
    {
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      if addr != entry.addr {
        forall val : Value
          ensures !OnEvictInProgress(c, v, addr, val)
          ensures !OnWritebackInProgress(c, v, addr, val)
        {
          assert !OnEvictInProgress(c, v, addr, val) by {
            assert !InFlightOnEvictRequest(c, v, addr, val) by {
              reveal InFlightOnEvictRequest;
              if idx: nat :| IsInFlightOnEvictRequest(c, v, addr, idx, val) {
                assert IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert OnEvictInProgress(c, v', addr, val);
                assert false;
              }
            }
            assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
              reveal CallbackPresent;
              if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnEvict(val) {
                assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
                assert OnEvictInProgress(c, v', addr, val);
                assert false;
              }
            }
          }
          assert !OnWritebackInProgress(c, v, addr, val) by {
            assert !InFlightOnWritebackRequest(c, v, addr, val) by {
              reveal InFlightOnWritebackRequest;
              if idx: nat :| IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
                assert IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert OnWritebackInProgress(c, v', addr, val);
                assert false;
              }
            }
            assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
              reveal CallbackPresent;
              if tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnWriteBack(val) {
                assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
                assert OnWritebackInProgress(c, v', addr, val);
                assert false;
              }
            }
          }
        }
        if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
          forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
            ensures (
              || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
              || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
              || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
            )
          {
            assert v.tiles[addr.morphType.idx].l2 == v'.tiles[addr.morphType.idx].l2;
            assert NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx);
            if v'.tiles[addr.morphType.idx].l2.cache[idx].addr != addr {
              assert v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr;
            } else {
              assert v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
              if InFlightOnMissRequest(c, v', addr, idx) {
                reveal InFlightOnMissRequest;
                var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
                assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
                assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
              } else {
                assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                  && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                  && !v'.tiles[tile].engine.buffer[buf].started;
                assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
                assert (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
              }
            }
          }
        }
        if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
          forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
            ensures (
              || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
              || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
              || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
            )
          {
            assert v.tiles[c.addr_map(addr)].l3 == v'.tiles[c.addr_map(addr)].l3;
            assert NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx);
            if v'.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr {
              assert v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr;
            } else {
              assert v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?; 
              if InFlightOnMissRequest(c, v', addr, idx) { 
                reveal InFlightOnMissRequest;
                var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, idx);
                assert IsInFlightOnMissRequest(c, v, addr, req_idx, idx);
                assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx));
              } else {
                assert UnstartedCallbackPresent(c, v', addr, EngineRequest.OnMiss(idx));
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
                  && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(idx)
                  && !v'.tiles[tile].engine.buffer[buf].started;
                assert UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx));
                assert (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)));
              }
            }
          }
        }
        assert v.g.callback_epochs[addr].Out?;
      } else {
        if re == EndOnMiss {
          assert entry.cb_type.OnMiss?;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          var msg :| msg in step.msgOps.send;
          assert IsInFlightOnMissResponse(c, v', addr, msg, entry.cb_type.idx);
          assert InFlightOnMissResponse(c, v', addr, entry.cb_type.idx) by { reveal InFlightOnMissResponse; }
          assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
          assert OnMissInProgress(c, v, addr, entry.cb_type.idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert InFlightOnMissRequest(c, v', addr, entry.cb_type.idx) || UnstartedCallbackPresent(c, v', addr, entry.cb_type);
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert InFlightOnMissRequest(c, v', addr, entry.cb_type.idx) || UnstartedCallbackPresent(c, v', addr, entry.cb_type);
          }
          if InFlightOnMissRequest(c, v', addr, entry.cb_type.idx) {
            reveal InFlightOnMissRequest;
            var req_idx :| IsInFlightOnMissRequest(c, v', addr, req_idx, entry.cb_type.idx);
            assert IsInFlightOnMissRequest(c, v, addr, req_idx, entry.cb_type.idx);
            assert InFlightOnMissRequest(c, v, addr, entry.cb_type.idx);
          } else {
            assert UnstartedCallbackPresent(c, v', addr, entry.cb_type);
            reveal UnstartedCallbackPresent;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) 
              && v'.tiles[tile].engine.buffer[buf].cb_type == entry.cb_type
              && !v'.tiles[tile].engine.buffer[buf].started;
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
            assert false;
          }
        }
      }
    }
  }
}