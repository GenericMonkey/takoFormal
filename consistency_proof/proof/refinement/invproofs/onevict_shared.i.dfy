include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnEvictInProgressSharedProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes


  lemma CoreNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma ProxyNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma MemoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1: nat
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        if IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val) {
          if loc.addr == step.msgOps.recv.val.meta.addr {
            assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1 + 1, val);
            assert false;
          } else {
            assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
            assert false;
          }
        }
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      if CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val)) {
        assert loc.addr == step.msgOps.recv.val.meta.addr;
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, 0, val);
        assert false;
      }
    }
  }

  lemma EngineNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    if step.tile_step.eng_step.ReceiveCallbackReqStep? {
      EngineReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
    } else {
      EngineNotReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
    }
  }

  lemma L2NoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma L3ReqMemoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma L3RespMemoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma L3DirectoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      if loc.addr != step.msgOps.recv.val.meta.addr {
        assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
        assert !OnEvictInProgress(c, v, loc.addr, val);
      } else {
        assert IsInFlightOnMissResponse(c, v, loc.addr, step.msgOps.recv.val, step.msgOps.recv.val.engine_resp.idx);
        assert InFlightOnMissResponse(c, v, loc.addr, step.msgOps.recv.val.engine_resp.idx) by { reveal InFlightOnMissResponse; }
        assert !OnEvictInProgress(c, v, loc.addr, val);
      }
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1: nat
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        if IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val) {
          assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
          var msg :| msg in step.msgOps.send;
          assert v'.network.inFlightEngReqs[loc.addr][idx1] == msg;
          assert idx1 == if loc.addr in v.network.inFlightEngReqs then |v.network.inFlightEngReqs[loc.addr]| else 0;
          assert core == step.tile_idx;
          if idx == step.tile_step.l3_step.idx {
            assert !NonEmptyL3CacheEntry(c, v', core, idx);
            assert false;
          } else {
            assert false;
          }

        }
      }
      assert !InFlightOnEvictRequest(c, v', v'.tiles[core].l3.cache[idx].addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', v'.tiles[core].l3.cache[idx].addr, EngineRequest.OnEvict(val));
    }
  }

  lemma L3NoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    match step.tile_step.l3_step {
      case ReqMemoryStep(_, _) => {
        L3ReqMemoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
      }
      case RespMemoryStep(_) => {
        L3RespMemoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
      }
      case DirectoryStep(_, _, _) => {
        L3DirectoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
      }
      case ScheduleCallbackStep(_, _, _) => {
        L3ScheduleCallbackNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
      }
      case ReceiveOnMissDataStep(_) => {
        L3ReceiveOnMissDataNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
      }
      case ReceiveCoherenceMessageStep() => {
        L3ReceiveCoherenceMessageNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
      }
    }
  }

  lemma NoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        MemoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesExistingCacheEntryMeansNoEvictInProgressShared(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }

  lemma StartEndCBPreservesExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnEvictRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnEvict(val));
    }
  }
}