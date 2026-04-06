include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnEvictInProgressPrivateProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes


  lemma CoreNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma ProxyNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma MemoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma L3NoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1: nat
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        if IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val) {
          assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
          assert false;
        }
      }
      assert !InFlightOnEvictRequest(c, v', v'.tiles[core].l2.cache[idx].addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', v'.tiles[core].l2.cache[idx].addr, EngineRequest.OnEvict(val));
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    assert step.tile_step.eng_step.CacheCommunicationStep?;
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma EngineReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma EngineNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    if step.tile_step.eng_step.ReceiveCallbackReqStep? {
      EngineReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
    } else {
      EngineNotReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
    }
  }

  lemma L2CacheCommunicationNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma L2DirectoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma L2ReceiveCoherenceMessageNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma L2ReceiveOnMissDataNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      // q: why isn't there a onevict rn?
      // pendingcb can have onevict
      // onmiss response existing means no evict
      var loc := v.tiles[core].l2.cache[idx];
      if loc.addr != step.msgOps.recv.val.meta.addr {
        assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma L2ScheduleCallbackNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2AddressesUnique(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnEvictInProgress(c, v, loc.addr, val);
      assert !InFlightOnEvictRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnEvict(val));
      reveal InFlightOnEvictRequest;
      forall idx1: nat
        ensures !IsInFlightOnEvictRequest(c, v', loc.addr, idx1, val)
      {
        if IsInFlightOnEvictRequest(c, v', loc.addr, idx1,val) {
          assert !IsInFlightOnEvictRequest(c, v, loc.addr, idx1, val);
          var msg :| msg in step.msgOps.send;
          assert v'.network.inFlightEngReqs[loc.addr][idx1] == msg;
          assert idx1 == if loc.addr in v.network.inFlightEngReqs then |v.network.inFlightEngReqs[loc.addr]| else 0;
          assert core == step.tile_idx;
          if idx == step.tile_step.l2_step.idx {
            assert !NonEmptyL2CacheEntry(c, v', core, idx);
            assert false;
          } else {
            assert false;
          }

        }
      }
      assert !InFlightOnEvictRequest(c, v', v'.tiles[core].l2.cache[idx].addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', v'.tiles[core].l2.cache[idx].addr, EngineRequest.OnEvict(val));
    }
  }

  lemma L2NoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2AddressesUnique(c, v)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    match step.tile_step.l2_step {
      case ReceiveCoherenceMessageStep() => {
        L2ReceiveCoherenceMessageNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
      }
      case CacheCommunicationStep(_, _, _, _) => {
        L2CacheCommunicationNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
      }
      case DirectoryStep(_, _, _) => {
        L2DirectoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
      }
      case ScheduleCallbackStep(_, _, _) => {
        L2ScheduleCallbackNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
      }
      case ReceiveOnMissDataStep(_) => {
        L2ReceiveOnMissDataNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
      }
    }
  }

  lemma NoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2AddressesUnique(c, v)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        MemoryNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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

  lemma StartEndCBPreservesExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    ensures ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
    )
      ensures (
        !OnEvictInProgress(c, v', v'.tiles[core].l2.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l2.cache[idx];
      assert NonEmptyL2CacheEntry(c, v, core, idx) && !loc.PendingCB?;
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