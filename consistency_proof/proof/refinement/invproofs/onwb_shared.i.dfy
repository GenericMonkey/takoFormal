include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnWritebackInProgressSharedProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma ProxyNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma MemoryNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1: nat
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        if IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val) {
          if loc.addr == step.msgOps.recv.val.meta.addr {
            assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1 + 1, val);
            assert false;
          } else {
            assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
            assert false;
          }
        }
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      if CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val)) {
        assert loc.addr == step.msgOps.recv.val.meta.addr;
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, 0, val);
        assert false;
      }
    }
  }

  lemma EngineNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    if step.tile_step.eng_step.ReceiveCallbackReqStep? {
      EngineReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
    } else {
      EngineNotReceiveCallbackReqNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
    }
  }

  lemma L2NoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma L3ReqMemoryNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma L3RespMemoryNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma L3DirectoryNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires v.WF(c)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      if loc.addr != step.msgOps.recv.val.meta.addr {
        assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
        assert !OnWritebackInProgress(c, v, loc.addr, val);
      } else {
        assert IsInFlightOnMissResponse(c, v, loc.addr, step.msgOps.recv.val, step.msgOps.recv.val.engine_resp.idx);
        assert InFlightOnMissResponse(c, v, loc.addr, step.msgOps.recv.val.engine_resp.idx) by { reveal InFlightOnMissResponse; }
        assert !OnWritebackInProgress(c, v, loc.addr, val);
      }
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1: nat
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        if IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val) {
          assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
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
      assert !InFlightOnWritebackRequest(c, v', v'.tiles[core].l3.cache[idx].addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', v'.tiles[core].l3.cache[idx].addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma L3NoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    match step.tile_step.l3_step {
      case ReqMemoryStep(_, _) => {
        L3ReqMemoryNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
      }
      case RespMemoryStep(_) => {
        L3RespMemoryNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
      }
      case DirectoryStep(_, _, _) => {
        L3DirectoryNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
      }
      case ScheduleCallbackStep(_, _, _) => {
        L3ScheduleCallbackNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
      }
      case ReceiveOnMissDataStep(_) => {
        L3ReceiveOnMissDataNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
      }
      case ReceiveCoherenceMessageStep() => {
        L3ReceiveCoherenceMessageNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
      }
    }
  }

  lemma NoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        MemoryNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }

  lemma StartEndCBPreservesExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    ensures ExistingCacheEntryMeansNoWritebackInProgressShared(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v', core, idx)
      && !v'.tiles[core].l3.cache[idx].PendingCB?
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
      ensures (
        !OnWritebackInProgress(c, v', v'.tiles[core].l3.cache[idx].addr, val)
      )
    {
      var loc := v.tiles[core].l3.cache[idx];
      assert NonEmptyL3CacheEntry(c, v, core, idx) && !loc.PendingCB?;
      assert !OnWritebackInProgress(c, v, loc.addr, val);
      assert !InFlightOnWritebackRequest(c, v, loc.addr, val);
      assert !CallbackPresent(c, v, loc.addr, EngineRequest.OnWriteBack(val));
      reveal InFlightOnWritebackRequest;
      forall idx1
        ensures !IsInFlightOnWritebackRequest(c, v', loc.addr, idx1, val)
      {
        assert !IsInFlightOnWritebackRequest(c, v, loc.addr, idx1, val);
      }
      assert !InFlightOnWritebackRequest(c, v', loc.addr, val);
      reveal CallbackPresent;
      assert !CallbackPresent(c, v', loc.addr, EngineRequest.OnWriteBack(val));
    }
  }
}