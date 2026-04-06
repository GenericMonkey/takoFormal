include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module DirtyBitPropertiesProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }
  
  lemma ProxyNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }

  lemma EngineNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }

  lemma L2CacheCommunicationNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }

  lemma L2DirectoryNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }

  lemma L3NoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }

  lemma MemoryNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
    ensures (
      && AddrIsInEpoch(c, v', addr)
      && v'.g.callback_epochs[addr].wcb.None?
      && v'.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
    ) {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
    }
  }

  
  lemma NoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    match step {
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(core_step) => {
            CoreNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnMissResponseMeansInEpochWithNoWrite(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
      ensures (
        && AddrIsInEpoch(c, v', addr)
        && v'.g.callback_epochs[addr].wcb.None?
        && v'.g.callback_epochs[addr].me.Me?
        && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
      )
    {
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx) by {
        reveal InFlightOnMissResponse;
      }
      assert OnMissInProgress(c, v, addr, c_idx);
      var inst := if step.tile_step.CoreStep? then step.tile_step.core_step.inst else step.tile_step.eng_step.inst;
      if inst.RMW? || inst.Store? {
        if inst.addr == addr {
          if PrivateMorph(addr) {
            assert step.tile_idx == addr.morphType.idx;
            reveal L2PendingCallbackForAddr;
            assert L2AddrNotInCache(c, v, step.tile_idx, addr);
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, step.tile_idx, addr);
            assert false;
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesOnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissResponseMeansInEpochWithNoWrite(c, v')
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v', addr, msg, c_idx) 
      ensures (
        && AddrIsInEpoch(c, v', addr)
        && v'.g.callback_epochs[addr].wcb.None?
        && v'.g.callback_epochs[addr].me.Me?
        && msg.engine_resp.val == v'.g.callback_epochs[addr].me.val
      )
    {
      if IsInFlightOnMissResponse(c, v, addr, msg, c_idx)
        && addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr
      {
        assert InFlightOnMissResponse(c, v, addr, c_idx) by {
          reveal InFlightOnMissResponse;
        }
        forall val: Value 
          ensures !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val))
          ensures !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val))
        {
          assert !OnEvictInProgress(c, v, addr, val);
          assert !OnWritebackInProgress(c, v, addr, val);
        }
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert other_idx != c_idx;
          assert OnMissInProgress(c, v, addr, c_idx);
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert false;
          }
        }
      } 
    }
  }

  lemma MemoryNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma ProxyNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L3NoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }
  
  lemma L2DirectoryNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires L1AddressesUnique(c, v)
    requires EL1AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }

      if (!DirML2CacheEntry(c, v, core, idx) 
        || (DirML2CacheEntry(c, v, core, idx) && v'.tiles[core].l2.cache[idx].dir.owner != v.tiles[core].l2.cache[idx].dir.owner)
      ) {
        assert step.tile_step.l2_step.msg.coh_msg.GetM?;
        assert GetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2)) by {
          reveal GetMInFlight;
          assert step.tile_step.l2_step.msg.coh_msg.GetM?;
          assert step.tile_step.l2_step.msg.meta.src == v'.tiles[core].l2.cache[idx].dir.owner;
        }
        assert false;
      } 
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }
  
  lemma L2ScheduleCallbackNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma CoreNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      if !PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) {
        reveal PutMInFlight;
        assert core == step.tile_idx;
        assert step.tile_step.core_step.step.EvictStep?;
        assert v.tiles[core].core.cache[step.tile_step.core_step.idx].coh.M?;
        assert v.tiles[core].core.cache[step.tile_step.core_step.idx].dirty;
      }
    }
  }

  
  lemma EngineNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      if !PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) {
        reveal PutMInFlight;
        assert core == step.tile_idx;
        assert step.tile_step.eng_step.step.EvictStep?;
        assert v.tiles[core].engine.cache[step.tile_step.eng_step.c_idx].coh.M?;
        assert v.tiles[core].engine.cache[step.tile_step.eng_step.c_idx].dirty;
      }
    }
  }

  lemma NoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires L1AddressesUnique(c, v)
    requires EL1AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case ProxyStep(_) => {
            ProxyNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
          }
          case L3Step(_) => {
            L3NoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
            }
          }
          case CoreStep(_) => {
            CoreNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesPutMFromOwnerL2MeansInterveningWrite(c, v, v', step);
          }
        }
      }
    }
  }
  
  lemma PerformNextInstPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma StartEndCBPreservesPutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    ensures PutMFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v'.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
      var addr := v'.tiles[core].l2.cache[idx].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            // assert CohML2CacheEntry(c, v, core, idx);
            // assert !L2AddrNotInCache(c, v, core, addr);
            // assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert false;
          }
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            // assert CohML2CacheEntry(c, v, core, idx);
            // assert !L2AddrNotInCache(c, v, core, addr);
            // assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert false;
          }
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert v.tiles[c.addr_map(addr)].l3.cache[other_idx].addr == addr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          }
        }
      } 
    }
  }
  
  lemma MemoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma ProxyNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma CoreNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma EngineNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2DirectoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  // l2ify for cache communication
  lemma L2CacheCommunicationNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      if !PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) {
        reveal PutMInFlight;
        assert step.tile_step.l2_step.c_step.EvictStep?;
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.idx].coh.M?;
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.idx].dirty;
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L3ReqMemoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }
  
  lemma L3RespMemoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L3DirectoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires L2AddressesUnique(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
      if (!DirML3CacheEntry(c, v, core, idx) 
        || (DirML3CacheEntry(c, v, core, idx) && v'.tiles[core].l3.cache[idx].dir.owner != v.tiles[core].l3.cache[idx].dir.owner)
      ) {
        assert step.tile_step.l3_step.msg.coh_msg.GetM?;
        assert GetMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3)) by {
          reveal GetMInFlight;
          assert step.tile_step.l3_step.msg.coh_msg.GetM?;
          assert step.tile_step.l3_step.msg.meta.src == v'.tiles[core].l3.cache[idx].dir.owner;
        }
        assert step.tile_step.l3_step.msg.meta.src.level.L2?;
        assert false;
      } 
    }
  }

  lemma NoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires L2AddressesUnique(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case ProxyStep(_) => {
            ProxyNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
            }
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
            }
          }
          case CoreStep(_) => {
            CoreNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesPutMFromOwnerL3MeansInterveningWrite(c, v, v', step);
          }
        }
      }
    }
  }
  
  lemma PerformNextInstPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma StartEndCBPreservesPutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    ensures PutMFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v', core, idx)
      && v'.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v'.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert PutMInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, v'.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val) by {
        reveal PutMInFlight;
      }
      var addr := v'.tiles[core].l3.cache[idx].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert SharedMorph(addr);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert SharedMorph(addr);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          assert SharedMorph(addr);
          reveal L3PendingCallbackForAddr;
          assert false;
        }
      } 
    }
  }

  lemma MemoryNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma ProxyNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L3NoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }
  
  lemma L2DirectoryNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires DataInFlightToT2FromT1MeansDirectoryInSD(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
      assert NonEmptyNonPendingL2CacheEntry(c, v, core, idx); //trigger
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }
  
  lemma L2ScheduleCallbackNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma CoreNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    // requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      if !DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) {
        reveal DataInFlight;
        assert core == step.tile_idx;
        assert step.tile_step.core_step.step.RecvMsgStep?;
        assert v.tiles[core].core.cache[step.tile_step.core_step.idx].addr == v'.tiles[core].l2.cache[idx].addr;
        if !v.tiles[core].core.cache[step.tile_step.core_step.idx].coh.M? {
          assert v.tiles[core].core.cache[step.tile_step.core_step.idx].coh.MIA?
            || v.tiles[core].core.cache[step.tile_step.core_step.idx].coh.MIF?;
          assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, step.msgOps.recv.val.meta.src, Cache(core, L1)) by {
            reveal FwdGetSInFlight;
            assert step.msgOps.recv.val.coh_msg.FwdGetS?;
          }
        }
      }
    }
  }

  
  lemma EngineNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    // requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      if !DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) {
        reveal DataInFlight;
        assert core == step.tile_idx;
        assert step.tile_step.eng_step.step.RecvMsgStep?;
        assert v.tiles[core].engine.cache[step.tile_step.eng_step.c_idx].addr == v'.tiles[core].l2.cache[idx].addr;
        if !v.tiles[core].engine.cache[step.tile_step.eng_step.c_idx].coh.M? {
          assert v.tiles[core].engine.cache[step.tile_step.eng_step.c_idx].coh.MIA?
            || v.tiles[core].engine.cache[step.tile_step.eng_step.c_idx].coh.MIF?;
          assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, step.msgOps.recv.val.meta.src, Cache(core, eL1)) by {
            reveal FwdGetSInFlight;
            assert step.msgOps.recv.val.coh_msg.FwdGetS?;
          }
          // assert step.msgOps.recv.val.meta.src != Cache(core, eL1);
          // assert step.msgOps.recv.val.meta.src.Cache?;
          // assert step.msgOps.recv.val.meta.src.level.Tier1();
          // assert step.msgOps.recv.val.meta.src == Cache(core, L1) || step.msgOps.recv.val.meta.src == Cache(core, Proxy);
          // assert DirSDL2CacheEntry(c, v, core, idx);
        }
      }
    }
  }
  lemma NoOpPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires DataInFlightToT2FromT1MeansDirectoryInSD(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case ProxyStep(_) => {
            ProxyNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
          }
          case L3Step(_) => {
            L3NoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
              }
            }
          }
          case CoreStep(_) => {
            CoreNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesDataFromOwnerL2MeansInterveningWrite(c, v, v', step);
          }
        }
      }
    }
  }
  
  lemma PerformNextInstPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma StartEndCBPreservesDataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    ensures DataFromOwnerL2MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val) by {
        reveal DataInFlight;
      }
      var addr := v'.tiles[core].l2.cache[idx].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            assert false;
          }
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            assert false;
          }
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert v.tiles[c.addr_map(addr)].l3.cache[other_idx].addr == addr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          }
        }
      } 
    }
  }

  lemma MemoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma ProxyNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma CoreNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma EngineNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2DirectoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2QueueHeadsWellformed(c, v)
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      if !DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) {
        reveal DataInFlight;
        assert step.tile_step.l2_step.c_step.RecvMsgStep?;
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.idx].addr == v'.tiles[core].l3.cache[idx].addr;
        if !v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.idx].coh.M? {
          assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.idx].coh.MIA?
            || v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.idx].coh.MIF?;
          assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.idx].dirty;
          // assert step.tile_step.l2_step.msg.coh_msg.FwdGetS? || step.tile_step.l2_step.msg.coh_msg.FwdGetM?;
          assert FwdGetSInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, step.tile_step.l2_step.msg.meta.src, Cache(step.tile_idx, L2)) by {
            reveal FwdGetSInFlight;
            assert step.tile_step.l2_step.msg.coh_msg.FwdGetS?;
          }
        }
      }
    }
  }
  
  lemma L3ReceiveCoherenceMessageNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L3ReqMemoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L3RespMemoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  // l3ify this one 
  lemma L3DirectoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires DataInFlightToT3FromT2MeansDirectoryInSD(c, v)
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
      assert NonEmptyNonPendingL3CacheEntry(c, v, core, idx); //trigger
    }
  }


  
  lemma NoOpPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires DataInFlightToT3FromT2MeansDirectoryInSD(c, v)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case ProxyStep(_) => {
            ProxyNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
            }
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
              }
            }
          }
          case CoreStep(_) => {
            CoreNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesDataFromOwnerL3MeansInterveningWrite(c, v, v', step);
          }
        }
      }
    }
  }
  
  lemma PerformNextInstPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma StartEndCBPreservesDataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    ensures DataFromOwnerL3MeansInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v', core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v', v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
    )
    ensures v'.g.callback_epochs[v'.tiles[core].l3.cache[idx].addr].wcb.Some?
    {
      assert DataInFlight(c, v, v'.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val) by {
        reveal DataInFlight;
      }
      var addr := v'.tiles[core].l3.cache[idx].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert SharedMorph(addr);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert SharedMorph(addr);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          assert SharedMorph(addr);
          reveal L3PendingCallbackForAddr;
          assert false;
        }
      } 
    }
  }
  
  lemma MemoryNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma CoreNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma EngineNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L3NoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
    }
  }

  lemma L2DirectoryNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2QueueHeadsWellformed(c, v)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires ProxyAddressesUnique(c, v)
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
      if step.tile_step.l2_step.msg.coh_msg.GetM? && step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy) && 
        v'.tiles[core].l2.cache[idx].addr == step.tile_step.l2_step.msg.meta.addr
      {
        assert GetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2)) by {
          reveal GetMInFlight;
        }
        assert false;
      }
    }
  }

  lemma ProxyNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      if !PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) {
        reveal PutMInFlight;
        assert core == step.tile_idx;
        assert step.tile_step.proxy_step.step.EvictStep?;
        assert v.tiles[core].proxy.cache[step.tile_step.proxy_step.idx].coh.M?;
        assert v.tiles[core].proxy.cache[step.tile_step.proxy_step.idx].addr == v'.tiles[core].l2.cache[idx].addr;
      }
    }
  }

  lemma NoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2QueueHeadsWellformed(c, v)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires ProxyAddressesUnique(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case ProxyStep(_) => {
            ProxyNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
          case L3Step(_) => {
            L3NoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
            }
          }
          case CoreStep(_) => {
            CoreNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires PutMFromOwnerMeansNoLoadableInCore(c, v)
    requires PutMFromOwnerMeansNoLoadableInEngine(c, v)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v) // core will match as its a private morph
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)

    requires MInCoreMeansMinL2(c, v)
    requires MInEngineMeansMinL2(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L2InCohMMeansAddrNotInOtherL2s(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)

    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v.tiles[core].l2.cache[idx].addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }
      assert DirML2CacheEntry(c, v, core, idx);
      var addr := v'.tiles[core].l2.cache[idx].addr;
      var inst := if step.tile_step.CoreStep? then step.tile_step.core_step.inst else step.tile_step.eng_step.inst;
      if inst.RMW? || inst.Store? {
        if inst.addr == addr {
          if step.tile_step.CoreStep? {
            var entry := v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx];
            assert entry.addr == addr;
            assert entry.coh.M?;
            if step.tile_idx == core {
              assert false;
            } else {
              assert !L2AddrNotInCache(c, v, step.tile_idx, entry.addr);
              var idx: nat :| NonEmptyL2CacheEntry(c, v, step.tile_idx, idx)
                && v.tiles[step.tile_idx].l2.cache[idx].addr == addr;
              assert CohML2CacheEntry(c, v, step.tile_idx, idx);
              assert L2AddrNotInCache(c, v, core, addr);
              assert false;
            }
          } else {
            var entry := v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx];
            assert entry.addr == addr;
            assert entry.coh.M?;
            if step.tile_idx == core {
              assert false;
            } else {
              assert !L2AddrNotInCache(c, v, step.tile_idx, entry.addr);
              var idx: nat :| NonEmptyL2CacheEntry(c, v, step.tile_idx, idx)
                && v.tiles[step.tile_idx].l2.cache[idx].addr == addr;
              assert CohML2CacheEntry(c, v, step.tile_idx, idx);
              assert L2AddrNotInCache(c, v, core, addr);
              assert false;
            }
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesPutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert PutMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, v'.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val) by {
        reveal PutMInFlight;
      }

      var addr := v'.tiles[core].l2.cache[idx].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            assert false;
          }
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            assert false;
          }
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          }
        }
      } 
    }
  }

  lemma MemoryNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }
  
  lemma CoreNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma EngineNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L3NoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2DirectoryNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires DataInFlightToT2FromT1MeansDirectoryInSD(c, v)
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
      assert NonEmptyNonPendingL2CacheEntry(c, v, core, idx); // additional trigger
    }
  }

  lemma ProxyNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    requires L2AddressesUnique(c, v)
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      if !DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) {
        reveal DataInFlight;
        assert core == step.tile_idx;
        assert step.tile_step.proxy_step.step.RecvMsgStep?;
        assert v.tiles[core].proxy.cache[step.tile_step.proxy_step.idx].coh.M?
          || v.tiles[core].proxy.cache[step.tile_step.proxy_step.idx].coh.MIA?
          || v.tiles[core].proxy.cache[step.tile_step.proxy_step.idx].coh.MIF?;
      }
    }
  }

  lemma NoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    requires L2AddressesUnique(c, v)
    requires DataInFlightToT2FromT1MeansDirectoryInSD(c, v)
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case ProxyStep(_) => {
            ProxyNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
          case L3Step(_) => {
            L3NoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
            }
          }
          case CoreStep(_) => {
            CoreNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
        }
      }
    }
  }

  
  lemma PerformNextInstPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2DirectoryInSDAndMInCoreMeansFormerOwner(c, v)
    requires L2DirectoryInSDAndMInEngineMeansFormerOwner(c, v)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v) // core will match as its a private morph
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)

    requires MInCoreMeansMinL2(c, v)
    requires MInEngineMeansMinL2(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L2InCohMMeansAddrNotInOtherL2s(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)

    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
      assert DirSDL2CacheEntry(c, v, core, idx);
      var addr := v'.tiles[core].l2.cache[idx].addr;
      var inst := if step.tile_step.CoreStep? then step.tile_step.core_step.inst else step.tile_step.eng_step.inst;
      if inst.RMW? || inst.Store? {
        if inst.addr == addr {
          if step.tile_step.CoreStep? {
            var entry := v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx];
            assert entry.addr == addr;
            assert entry.coh.M?;
            if step.tile_idx == core {
              assert false;
            } else {
              assert !L2AddrNotInCache(c, v, step.tile_idx, entry.addr);
              var idx: nat :| NonEmptyL2CacheEntry(c, v, step.tile_idx, idx)
                && v.tiles[step.tile_idx].l2.cache[idx].addr == addr;
              assert CohML2CacheEntry(c, v, step.tile_idx, idx);
              assert L2AddrNotInCache(c, v, core, addr);
              assert false;
            }
          } else {
            var entry := v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx];
            assert entry.addr == addr;
            assert entry.coh.M?;
            if step.tile_idx == core {
              assert false;
            } else {
              assert !L2AddrNotInCache(c, v, step.tile_idx, entry.addr);
              var idx: nat :| NonEmptyL2CacheEntry(c, v, step.tile_idx, idx)
                && v.tiles[step.tile_idx].l2.cache[idx].addr == addr;
              assert CohML2CacheEntry(c, v, step.tile_idx, idx);
              assert L2AddrNotInCache(c, v, core, addr);
              assert false;
            }
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesDataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)

    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v', core, idx)
      && v'.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
      ensures (
        && (DirtyL2CacheEntry(c, v', core, idx) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
          && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
        ))
      )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val) by {
        reveal DataInFlight;
      }
      var addr := v'.tiles[core].l2.cache[idx].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
          }
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            assert false;
          }
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          } 
        }
      } 
    }
  }

  lemma NotCoreNoOpPreservesDirtyMorphAddressMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires !step.tile_step.CoreStep?
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteCore(c, v')
  {}

  lemma MemoryNoOpPreservesDirtyMorphAddressMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteCore(c, v')
  {}

  lemma CoreNoOpPreservesDirtyMorphAddressMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires PreMStateMeansNotDirtyCore(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx)
      && v'.tiles[core].core.cache[idx].dirty
      && v'.tiles[core].core.cache[idx].coh.Loadable()
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx].addr)
    ) 
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx].addr].wcb.Some?
    )
    {}
  }

  lemma NoOpPreservesDirtyMorphAddressMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires PreMStateMeansNotDirtyCore(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteCore(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesDirtyMorphAddressMeansInterveningWriteCore(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        if tile_step.CoreStep? {
          CoreNoOpPreservesDirtyMorphAddressMeansInterveningWriteCore(c, v, v', step);
        }
        else {
          NotCoreNoOpPreservesDirtyMorphAddressMeansInterveningWriteCore(c, v, v', step);
        }
      }
    }
  }
  
  lemma PerformNextInstPreservesDirtyMorphAddressMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L1AddressesUnique(c, v)
    requires EpochEntryInMorphWorkingSet(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx)
      && v'.tiles[core].core.cache[idx].dirty
      && v'.tiles[core].core.cache[idx].coh.Loadable()
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx].addr)
    ) 
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx].addr].wcb.Some?
    )
    {
      var addr := v.tiles[core].core.cache[idx].addr;
      assert addr.Morph?;
    }
  }

  lemma StartEndCBPreservesDirtyMorphAddressMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)

    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx)
      && v'.tiles[core].core.cache[idx].dirty
      && v'.tiles[core].core.cache[idx].coh.Loadable()
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx].addr)
    ) 
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx].addr].wcb.Some?
    )
    {
      var addr := v'.tiles[core].core.cache[idx].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          assert CBOrderTrackerValidIndex(c, v, addr, step.tile_idx, 0);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          } else {
            reveal L3PendingCallbackForAddr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          }
        }
      } 
    }
  }

  
  lemma NotEngineNoOpPreservesDirtyMorphAddressMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires !step.tile_step.EngineStep?
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteEngine(c, v')
  {}

  lemma MemoryNoOpPreservesDirtyMorphAddressMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteEngine(c, v')
  {}

  lemma EngineNoOpPreservesDirtyMorphAddressMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires PreMStateMeansNotDirtyEngine(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyEL1CacheEntry(c, v', core, idx)
      && v'.tiles[core].engine.cache[idx].dirty
      && v'.tiles[core].engine.cache[idx].coh.Loadable()
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx].addr)
    ) 
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx].addr].wcb.Some?
    )
    {}
  }

  lemma NoOpPreservesDirtyMorphAddressMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires PreMStateMeansNotDirtyEngine(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteEngine(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesDirtyMorphAddressMeansInterveningWriteEngine(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        if tile_step.EngineStep? {
          EngineNoOpPreservesDirtyMorphAddressMeansInterveningWriteEngine(c, v, v', step);
        }
        else {
          NotEngineNoOpPreservesDirtyMorphAddressMeansInterveningWriteEngine(c, v, v', step);
        }
      }
    }
  }

  lemma PerformNextInstPreservesDirtyMorphAddressMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EL1AddressesUnique(c, v)
    requires EpochEntryInMorphWorkingSet(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyEL1CacheEntry(c, v', core, idx)
      && v'.tiles[core].engine.cache[idx].dirty
      && v'.tiles[core].engine.cache[idx].coh.Loadable()
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx].addr)
    ) 
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx].addr].wcb.Some?
    )
    {
      var addr := v.tiles[core].engine.cache[idx].addr;
      assert addr.Morph?;
    }
  }

  lemma StartEndCBPreservesDirtyMorphAddressMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)

    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    ensures DirtyMorphAddressMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyEL1CacheEntry(c, v', core, idx)
      && v'.tiles[core].engine.cache[idx].dirty
      && v'.tiles[core].engine.cache[idx].coh.Loadable()
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx].addr)
    ) 
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx].addr].wcb.Some?
    )
    {
      var addr := v'.tiles[core].engine.cache[idx].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          assert CBOrderTrackerValidIndex(c, v, addr, step.tile_idx, 0);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          } else {
            reveal L3PendingCallbackForAddr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          }
        }
      } 
    }
  }

  lemma EngineNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma MemoryNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma CoreNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma L3NoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.M?
        || v'.tiles[core].proxy.cache[idx1].coh.IMA?
        || v'.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      if !NonEmptyL2CacheEntry(c, v, core, idx2) {
        assert step.tile_step.l2_step.eng_req.OnMiss?;
        assert L2AddrNotInCache(c, v, core, v'.tiles[core].proxy.cache[idx1].addr);
        assert false;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires L2AddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.M?
        || v'.tiles[core].proxy.cache[idx1].coh.IMA?
        || v'.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      if !CleanL2CacheEntry(c, v, core, idx2) && CleanL2CacheEntry(c, v', core, idx2) {
        assert L2AddrNotInCache(c, v, core, v'.tiles[core].proxy.cache[idx1].addr);
        assert false;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires L2AddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.M?
        || v'.tiles[core].proxy.cache[idx1].coh.IMA?
        || v'.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      var addr := v'.tiles[core].proxy.cache[idx1].addr;
      if step.tile_idx == core && step.tile_step.l2_step.idx == idx2 && step.tile_step.l2_step.addr == addr {
        if !L2AddrNotInCache(c, v, core, addr) && step.tile_step.l2_step.c_step.GetMStep? {
          assert CohSToML2CacheEntry(c, v, core, idx2);
        }
      }
    }
  }

  lemma L2DirectoryNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires ProxyAddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires GetSInFlightToT2MeansSourceIsTransitioningToS(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.M?
        || v'.tiles[core].proxy.cache[idx1].coh.IMA?
        || v'.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      if step.tile_idx == core && step.tile_step.l2_step.opt_idx == Some(idx2) {
        if step.tile_step.l2_step.msg.coh_msg.PutM? 
          && DirML2CacheEntry(c, v, core, idx2)
          && step.tile_step.l2_step.msg.meta.src == v.tiles[core].l2.cache[idx2].dir.owner
        {
          assert PutMInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, v.tiles[core].l2.cache[idx2].dir.owner, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
            reveal PutMInFlight;
          }
        } 
        if step.tile_step.l2_step.msg.coh_msg.Data? 
          && DirSDL2CacheEntry(c, v, core, idx2)
          && step.tile_step.l2_step.msg.meta.src == v.tiles[core].l2.cache[idx2].dir.former_owner
        {
          assert DataInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, v.tiles[core].l2.cache[idx2].dir.former_owner, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
            reveal DataInFlight;
          }
        }
        if step.tile_step.l2_step.msg.coh_msg.GetM? 
          && DirML2CacheEntry(c, v, core, idx2)
          && step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy)
        {
          assert GetMInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, Cache(core, Proxy), Cache(core, L2)) by {
            reveal GetMInFlight;
          }
          var idx: nat :| NonEmptyProxyCacheEntry(c, v, core, idx) 
            && v.tiles[core].proxy.cache[idx].addr == v.tiles[core].l2.cache[idx2].addr 
            && (v.tiles[core].proxy.cache[idx].coh.IMAD? || v.tiles[core].proxy.cache[idx].coh.SMAD?);
          assert false;
        }
        // new case that can make us dirty as fwdgets now preemptively marks as well
        if step.tile_step.l2_step.msg.coh_msg.GetS? 
          && DirML2CacheEntry(c, v, core, idx2)
          && step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy)
        {
          assert GetSInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, Cache(core, Proxy), Cache(core, L2)) by {
            reveal GetSInFlight;
          }
          var idx: nat :| NonEmptyProxyCacheEntry(c, v, core, idx) 
            && v.tiles[core].proxy.cache[idx].addr == v.tiles[core].l2.cache[idx2].addr 
            && v.tiles[core].proxy.cache[idx].coh.ISD?;
          assert false;
        }
      }
    }
  }

  lemma ProxyNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.M?
        || v'.tiles[core].proxy.cache[idx1].coh.IMA?
        || v'.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      if step.tile_step.proxy_step.step.RecvMsgStep?
        && step.tile_idx == core
        && step.msgOps.recv.val.coh_msg.Data?
        && step.msgOps.recv.val.meta.addr == v'.tiles[core].proxy.cache[idx1].addr
      {
        var addr := v'.tiles[core].l2.cache[idx2].addr;
        assert DataInFlight(c, v, addr, step.msgOps.recv.val.meta.src, Cache(core, Proxy), step.msgOps.recv.val.coh_msg.val) by {
          reveal DataInFlight;
        }
        assert NonEmptyL2CacheEntry(c, v, core, idx2);
        // can show directory is in M, as the additional assumption for datainflight?
      }
    }
  }

  lemma NoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires ProxyAddressesUnique(c, v)
    requires L2AddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    // requires L2CohSToMMeansL2DirSorI(c, v)
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires GetSInFlightToT2MeansSourceIsTransitioningToS(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        if tile_step.EngineStep? {
          EngineNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);
        } else if tile_step.CoreStep? {
          CoreNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);
        } else if tile_step.L2Step? {
          if tile_step.l2_step.ReceiveCoherenceMessageStep? {
            L2ReceiveCoherenceMessageNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);
          } else if tile_step.l2_step.ScheduleCallbackStep? {
            L2ScheduleCallbackNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);
          } else if tile_step.l2_step.ReceiveOnMissDataStep? {
            L2ReceiveOnMissDataNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);
          } else if tile_step.l2_step.CacheCommunicationStep? {
            L2CacheCommunicationNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);
          } else if tile_step.l2_step.DirectoryStep? {
            L2DirectoryNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);
          }
        } else if tile_step.ProxyStep? {
          ProxyNoOpPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step);
        }
      }
    }
  }

  lemma CorePerformNextInstPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.NextInstStep?
    requires L1InCohMMeansAddrNotInOtherL1s(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.M?
        || v'.tiles[core].proxy.cache[idx1].coh.IMA?
        || v'.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      var addr := v.tiles[core].proxy.cache[idx1].addr;
      var inst := step.tile_step.core_step.inst;
      if inst.RMW? || inst.Store? {
        if inst.addr == addr {
          var entry := v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx];
          assert entry.addr == addr;
          // assert CohML1CacheEntry(c, v, step.tile_idx, step.tile_step.core_step.idx);
          // assert v.tiles[core].engine.cache[idx].coh.Loadable();
          assert !ProxyAddrNotMostRecentVal(c, v, core, v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].addr);
          assert false; // the core can't be taking a step when we have the most recent data in proxy
        }
      } 
    }
  }

  lemma EnginePerformNextInstPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.NextInstStep?
    requires EL1InCohMMeansAddrNotInOtherL1s(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.M?
        || v'.tiles[core].proxy.cache[idx1].coh.IMA?
        || v'.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      var addr := v.tiles[core].proxy.cache[idx1].addr;
      var inst := step.tile_step.eng_step.inst;
      if inst.RMW? || inst.Store? {
        if inst.addr == addr {
          var entry := v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx];
          assert entry.addr == addr;
          // assert CohMEL1CacheEntry(c, v, step.tile_idx, step.tile_step.eng_step.c_idx);
          assert !ProxyAddrNotMostRecentVal(c, v, core, v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].addr);
          assert false; // the engine can't be taking a step when we have the most recent data in proxy
        }
      } 
    }
  }

  lemma PerformNextInstPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L1InCohMMeansAddrNotInOtherL1s(c, v)
    requires EL1InCohMMeansAddrNotInOtherL1s(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    if step.tile_step.CoreStep? {
      CorePerformNextInstPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step, re);
    }
    if step.tile_step.EngineStep? {
      EnginePerformNextInstPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v, v', step, re);
    }
  }

  lemma StartEndCBPreservesLoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires OnEvictInProgressMeansNoLoadableInProxy(c, v)
    requires OnWritebackInProgressMeansNoLoadableInProxy(c, v)
    
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    ensures LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.M?
        || v'.tiles[core].proxy.cache[idx1].coh.IMA?
        || v'.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      var addr := v'.tiles[core].proxy.cache[idx1].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          } else {
            reveal L3PendingCallbackForAddr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          } 
        }
      } 
    }
  }


  lemma OtherNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? ==> (
      || step.tile_step.ProxyStep?
      || step.tile_step.EngineStep?
      || step.tile_step.L3Step?
    )
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v')
  {}

  lemma CoreNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.owner == Cache(core, L1))
        || (DirSDL2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, L1))
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].core.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      if step.tile_idx == core
        && step.tile_step.core_step.idx == idx1
        && step.tile_step.core_step.CacheCommunicationStep?
        && step.tile_step.core_step.step.EvictStep?
        && v.tiles[core].core.cache[idx1].coh.M?
      {
        assert v.tiles[core].core.cache[idx1].dirty;
      }
    }
  }

  lemma L2NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires L1AddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.owner == Cache(core, L1))
        || (DirSDL2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, L1))
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].core.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      if step.tile_idx == core
        && step.tile_step.l2_step.DirectoryStep?
        && step.tile_step.l2_step.opt_idx.Some?
        && step.tile_step.l2_step.opt_idx.val == idx2
        && step.tile_step.l2_step.msg.coh_msg.GetM?
        && step.tile_step.l2_step.msg.meta.src == Cache(core, L1)
      {
        assert GetMInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, Cache(core, L1), Cache(core, L2)) by {
          reveal GetMInFlight;
        }
        var idx :| NonEmptyL1CacheEntry(c, v, core, idx) 
          && v.tiles[core].core.cache[idx].addr == v.tiles[core].l2.cache[idx2].addr;
      }
    }
  }

  lemma NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L1AddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v')
  {
    if step.TileStep? && step.tile_step.CoreStep? {
      CoreNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v, v', step);
    } else if step.TileStep? && step.tile_step.L2Step? {
      L2NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v, v', step);
    } else {
      OtherNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v, v', step);
    }
  }

  // need m => not in core etc for engine
  lemma PerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.owner == Cache(core, L1))
        || (DirSDL2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, L1))
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].core.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
    }
  }

  lemma StartEndCBPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.owner == Cache(core, L1))
        || (DirSDL2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, L1))
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].core.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var addr := v'.tiles[core].core.cache[idx1].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            assert CohML2CacheEntry(c, v, core, idx2);
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert false;
          }
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            assert CohML2CacheEntry(c, v, core, idx2);
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert false;
          }
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert CohML2CacheEntry(c, v, core, idx2);
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert v.tiles[c.addr_map(addr)].l3.cache[other_idx].addr == addr;
            // cohM L2 -> dirM/SD entry in L3
            assert false;
          }
        }
      } 
    }
  }

  lemma MemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma EngineNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma ProxyNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma CoreCacheCommunicationRecvMsgNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.RecvMsgStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }
  
  lemma CoreCacheCommunicationGetSNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetSStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma CoreCacheCommunicationGetMNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetMStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma CoreCacheCommunicationEvictNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.EvictStep?
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }

      if step.tile_idx == core
        && step.tile_step.core_step.idx == idx1
        && v.tiles[core].core.cache[idx1].coh.M?
      {
        assert v.tiles[core].core.cache[idx1].dirty;
      } 
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      if !FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) {
        reveal FwdGetSInFlight;
        assert DirML2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.opt_idx.val);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.owner == Cache(core, L1);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].addr == v'.tiles[core].core.cache[idx1].addr;
        assert step.tile_idx == core;
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3RespMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }
  
  lemma L3DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma NoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(core_step) => {
            assert core_step.CacheCommunicationStep?;
            match core_step.step {
              case GetSStep() => {
                CoreCacheCommunicationGetSNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case GetMStep() => {
                CoreCacheCommunicationGetMNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case EvictStep() => {
                CoreCacheCommunicationEvictNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case RecvMsgStep() => {
                CoreCacheCommunicationRecvMsgNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
            }
          }
          case EngineStep(_) => {
            EngineNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  // need m => not in core etc for engine
  lemma PerformNextInstPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma StartEndCBPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var addr := v'.tiles[core].core.cache[idx1].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
          assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
            reveal FwdGetSInFlight;
          }
          var idx: nat :| DirSDL2CacheEntry(c, v, core, idx)
            && v.tiles[core].l2.cache[idx].addr == addr
            && v.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, L1);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert CohML2CacheEntry(c, v, core, idx);
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            // assert v.tiles[c.addr_map(addr)].l3.cache[other_idx].addr == addr;
            // cohM L2 -> dirM/SD entry in L3
            assert false;
          }
        }
      } else {
        var src :| FwdGetSInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
        assert FwdGetSInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
          reveal FwdGetSInFlight;
        }
      }
    }
  }

  lemma MemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma EngineNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma ProxyNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma CoreCacheCommunicationGetMNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetMStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma CoreCacheCommunicationGetSNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetSStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma CoreCacheCommunicationRecvMsgNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.RecvMsgStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma CoreCacheCommunicationEvictNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.EvictStep?
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      if step.tile_idx == core
        && step.tile_step.core_step.idx == idx1
        && v.tiles[core].core.cache[idx1].coh.M?
      {
        assert v.tiles[core].core.cache[idx1].dirty;
      } 
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      if !FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) {
        reveal FwdGetMInFlight;
        assert DirML2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.opt_idx.val);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.owner == Cache(core, L1);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].addr == v'.tiles[core].core.cache[idx1].addr;
        assert step.tile_idx == core;
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3RespMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }
  
  lemma L3DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma NoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(core_step) => {
            assert core_step.CacheCommunicationStep?;
            match core_step.step {
              case GetSStep() => {
                CoreCacheCommunicationGetSNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case GetMStep() => {
                CoreCacheCommunicationGetMNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case RecvMsgStep() => {
                CoreCacheCommunicationRecvMsgNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case EvictStep() => {
                CoreCacheCommunicationEvictNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
            }
          }
          case EngineStep(_) => {
            EngineNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  // need m => not in core etc for engine
  lemma PerformNextInstPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma StartEndCBPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v')
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].core.cache[idx1].coh.MIA?
        || v'.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].core.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
    {
      var addr := v'.tiles[core].core.cache[idx1].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
          assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
            reveal FwdGetMInFlight;
          }
          var idx: nat :| 
            CohML2CacheEntry(c, v, core, idx)
            && v.tiles[core].l2.cache[idx].addr == addr;
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            // assert v.tiles[c.addr_map(addr)].l3.cache[other_idx].addr == addr;
            // cohM L2 -> dirM/SD entry in L3
            assert false;
          }
        }
      } else {
        var src :| FwdGetMInFlight(c, v', v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1));
        assert FwdGetMInFlight(c, v, v'.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)) by {
          reveal FwdGetMInFlight;
        }
      }
    }
  }

  lemma OtherNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? ==> (
      || step.tile_step.ProxyStep?
      || step.tile_step.CoreStep?
      || step.tile_step.L3Step?
    )
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v')
  {}

  lemma EngineNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.owner == Cache(core, eL1))
        || (DirSDL2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, eL1))
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].engine.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      if step.tile_idx == core
        && step.tile_step.eng_step.CacheCommunicationStep?
        && step.tile_step.eng_step.c_idx == idx1
        && step.tile_step.eng_step.step.EvictStep?
        && v.tiles[core].engine.cache[idx1].coh.M?
      {
        assert v.tiles[core].engine.cache[idx1].dirty;
      }
    }
  }

  lemma L2NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires EL1AddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.owner == Cache(core, eL1))
        || (DirSDL2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, eL1))
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].engine.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      if step.tile_idx == core
        && step.tile_step.l2_step.DirectoryStep?
        && step.tile_step.l2_step.opt_idx.Some?
        && step.tile_step.l2_step.opt_idx.val == idx2
        && step.tile_step.l2_step.msg.coh_msg.GetM?
        && step.tile_step.l2_step.msg.meta.src == Cache(core, eL1)
      {
        assert GetMInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, Cache(core, eL1), Cache(core, L2)) by {
          reveal GetMInFlight;
        }
        var idx :| NonEmptyL1CacheEntry(c, v, core, idx) 
          && v.tiles[core].core.cache[idx].addr == v.tiles[core].l2.cache[idx2].addr;
      }
    }
  }

  lemma NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EL1AddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v')
  {
    if step.TileStep? && step.tile_step.EngineStep? {
      EngineNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v, v', step);
    } else if step.TileStep? && step.tile_step.L2Step? {
      L2NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v, v', step);
    } else {
      OtherNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v, v', step);
    }
  }

  // need m => not in core etc for engine
  lemma PerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.owner == Cache(core, eL1))
        || (DirSDL2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, eL1))
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].engine.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {}
  }

  lemma StartEndCBPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.owner == Cache(core, eL1))
        || (DirSDL2CacheEntry(c, v', core, idx2) && v'.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, eL1))
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].engine.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var addr := v'.tiles[core].engine.cache[idx1].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            assert CohML2CacheEntry(c, v, core, idx2);
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert false;
          }
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          if PrivateMorph(addr) {
            assert false;
          } else {
            assert SharedMorph(addr);
            assert CohML2CacheEntry(c, v, core, idx2);
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert false;
          }
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert CohML2CacheEntry(c, v, core, idx2);
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert v.tiles[c.addr_map(addr)].l3.cache[other_idx].addr == addr;
            // cohM L2 -> dirM/SD entry in L3
            assert false;
          }
        }
      } 
    }
  }
  
  lemma MemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma CoreNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma ProxyNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma EngineCacheCommunicationGetSNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetSStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
    }
  }
  
  lemma EngineCacheCommunicationGetMNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetMStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma EngineCacheCommunicationEvictNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.EvictStep?
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      if step.tile_idx == core
        && step.tile_step.eng_step.c_idx == idx1
        && v.tiles[core].engine.cache[idx1].coh.M?
      {
        assert v.tiles[core].engine.cache[idx1].dirty;
      } 
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      if !FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) {
        reveal FwdGetSInFlight;
        assert DirML2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.opt_idx.val);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.owner == Cache(core, eL1);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].addr == v'.tiles[core].engine.cache[idx1].addr;
        assert step.tile_idx == core;
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3RespMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }
  
  lemma L3DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma NoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.CacheCommunicationStep? {
              match eng_step.step {
                case GetSStep() => {
                  EngineCacheCommunicationGetSNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
                }
                case GetMStep() => {
                  EngineCacheCommunicationGetMNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
                }
                case RecvMsgStep() => {
                  EngineCacheCommunicationRecvMsgNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
                }
                case EvictStep() => {
                  EngineCacheCommunicationEvictNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
                }
              }
            } else {
              assert eng_step.ReceiveCallbackReqStep?;
              EngineReceiveCallbackReqNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  // need m => not in core etc for engine
  lemma PerformNextInstPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetSInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma StartEndCBPreservesMEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var addr := v'.tiles[core].engine.cache[idx1].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
          assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
            reveal FwdGetSInFlight;
          }
          var idx: nat :| DirSDL2CacheEntry(c, v, core, idx)
            && v.tiles[core].l2.cache[idx].addr == addr
            && v.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, eL1);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert CohML2CacheEntry(c, v, core, idx);
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            // assert v.tiles[c.addr_map(addr)].l3.cache[other_idx].addr == addr;
            // cohM L2 -> dirM/SD entry in L3
            assert false;
          }
        }
      } else {
        var src :| FwdGetSInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
        assert FwdGetSInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
          reveal FwdGetSInFlight;
        }
      }
    }
  }

  lemma MemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma CoreNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma ProxyNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma EngineCacheCommunicationGetSNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetSStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma EngineCacheCommunicationGetMNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetMStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma EngineCacheCommunicationEvictNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.EvictStep?
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      if step.tile_idx == core
        && step.tile_step.eng_step.c_idx == idx1
        && v.tiles[core].engine.cache[idx1].coh.M?
      {
        assert v.tiles[core].engine.cache[idx1].dirty;
      } 
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L2DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      if !FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) {
        reveal FwdGetMInFlight;
        assert DirML2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.opt_idx.val);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.owner == Cache(core, eL1);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].addr == v'.tiles[core].engine.cache[idx1].addr;
        assert step.tile_idx == core;
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3RespMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }
  
  lemma L3DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma NoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.CacheCommunicationStep? {
              match eng_step.step {
                case GetSStep() => {
                  EngineCacheCommunicationGetSNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
                }
                case GetMStep() => {
                  EngineCacheCommunicationGetMNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
                }
                case RecvMsgStep() => {
                  EngineCacheCommunicationRecvMsgNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
                }
                case EvictStep() => {
                  EngineCacheCommunicationEvictNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
                }
              }
            } else {
              assert eng_step.ReceiveCallbackReqStep?;
              EngineReceiveCallbackReqNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  // need m => not in core etc for engine
  lemma PerformNextInstPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
      assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
        reveal FwdGetMInFlight;
      }
      assert v.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?;
    }
  }

  lemma StartEndCBPreservesMEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    ensures MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v')
  {
    forall core: nat, idx1: nat/*, idx2: nat*/ | (
      && NonEmptyEL1CacheEntry(c, v', core, idx1)
      && (
        || v'.tiles[core].engine.cache[idx1].coh.MIA?
        || v'.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v', v'.tiles[core].engine.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
    {
      var addr := v'.tiles[core].engine.cache[idx1].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
          assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
            reveal FwdGetMInFlight;
          }
          var idx: nat :| 
            CohML2CacheEntry(c, v, core, idx)
            && v.tiles[core].l2.cache[idx].addr == addr;
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert v.tiles[core].l2.cache[idx].coh.Loadable();
            assert !L2AddrNotInCache(c, v, core, addr);
            assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            // assert v.tiles[c.addr_map(addr)].l3.cache[other_idx].addr == addr;
            // cohM L2 -> dirM/SD entry in L3
            assert false;
          }
        }
      } else {
        var src :| FwdGetMInFlight(c, v', v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1));
        assert FwdGetMInFlight(c, v, v'.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)) by {
          reveal FwdGetMInFlight;
        }
      }
    }
  }

  lemma CoreNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma MemoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma L3NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {}
  
  lemma EngineNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma ProxyNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.MIA?
        || v'.tiles[core].proxy.cache[idx1].coh.MIF?
      )
      && (
        || DirMProxyOwnerL2CacheEntry(c, v', core, idx2)
        || DirSDProxyOwnerL2CacheEntry(c, v', core, idx2)
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      if step.tile_idx == core
        && step.tile_step.proxy_step.idx == idx1
        && step.tile_step.proxy_step.step.EvictStep?
        && v.tiles[core].proxy.cache[idx1].coh.M?
      {
      }
    }
  }

  lemma L2DirectoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires ProxyAddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires GetSInFlightToT2MeansSourceIsTransitioningToS(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.MIA?
        || v'.tiles[core].proxy.cache[idx1].coh.MIF?
      )
      && (
        || DirMProxyOwnerL2CacheEntry(c, v', core, idx2)
        || DirSDProxyOwnerL2CacheEntry(c, v', core, idx2)
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      if step.tile_idx == core
        && step.tile_step.l2_step.opt_idx.Some?
        && step.tile_step.l2_step.opt_idx.val == idx2
        && (
          || step.tile_step.l2_step.msg.coh_msg.GetM?
          || step.tile_step.l2_step.msg.coh_msg.GetS?
        )
        && step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy)
      {
        if step.tile_step.l2_step.msg.coh_msg.GetM? {
          assert GetMInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, Cache(core, Proxy), Cache(core, L2)) by {
            reveal GetMInFlight;
          }
          var idx: nat :| NonEmptyProxyCacheEntry(c, v, core, idx) 
            && v.tiles[core].proxy.cache[idx].addr == v.tiles[core].l2.cache[idx2].addr
            && (
              || v.tiles[core].proxy.cache[idx].coh.IMAD?
              || v.tiles[core].proxy.cache[idx].coh.SMAD?
          );
          assert false;
        } else {
          assert GetSInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, Cache(core, Proxy), Cache(core, L2)) by {
            reveal GetSInFlight;
          }
          var idx: nat :| NonEmptyProxyCacheEntry(c, v, core, idx) 
            && v.tiles[core].proxy.cache[idx].addr == v.tiles[core].l2.cache[idx2].addr
            && v.tiles[core].proxy.cache[idx].coh.ISD?;
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires ProxyAddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires ProxyAddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires ProxyAddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires ProxyAddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {}

  lemma NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires ProxyAddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires GetSInFlightToT2MeansSourceIsTransitioningToS(c, v)
    requires LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
              }
            }
          }
          case L3Step(_) => {
            L3NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step);
          }
        }
      }
    }
  }

  lemma CorePerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.NextInstStep?
    requires ProxyAddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L2AddressesUnique(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L2InCohMMeansAddrNotInOtherL2s(c, v)
    requires MInCoreMeansMinL2(c, v)
    requires L2DirectoryInSDAndMInCoreMeansFormerOwner(c, v)
    requires L2DirectoryInMAndMInCoreMeansOwnerOrFwdGetMInFlight(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.MIA?
        || v'.tiles[core].proxy.cache[idx1].coh.MIF?
      )
      && (
        || DirMProxyOwnerL2CacheEntry(c, v', core, idx2)
        || DirSDProxyOwnerL2CacheEntry(c, v', core, idx2)
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      var addr := v.tiles[core].proxy.cache[idx1].addr;
      var inst := step.tile_step.core_step.inst;
      // dirM/SD means CohML2 for for 
      // assert CohML2CacheEntry(c, v, core, idx2);
      if inst.RMW? || inst.Store? {
        if inst.addr == addr {
          var entry := v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx];
          assert entry.addr == addr;
          assert CohML1CacheEntry(c, v, step.tile_idx, step.tile_step.core_step.idx);
          // cohMl1 means its in L2 for this core
          if core != step.tile_idx {
            assert !L2AddrNotInCache(c, v, step.tile_idx, addr);
            var idx: nat :| NonEmptyL2CacheEntry(c, v, step.tile_idx, idx)
              && v.tiles[step.tile_idx].l2.cache[idx].addr == addr;
            assert CohML2CacheEntry(c, v, step.tile_idx, idx);
            assert L2AddrNotInCache(c, v, core, addr);
            // because we aren't in I state, we must have it loadable, a contradiction
            assert !DirIL2CacheEntry(c, v, core, idx2);
            assert v.tiles[core].l2.cache[idx2].coh.Loadable();
            assert false;
          } else {
            // its m or sd with core owner, and we know its not the latter
            assert DirML2CacheEntry(c, v, core, idx2);
            var dst :| FwdGetMInFlight(c, v, addr, Cache(core, Proxy), dst);
            var idx :| NonEmptyProxyCacheEntry(c, v, core, idx)
              && v.tiles[core].proxy.cache[idx].addr == addr
              && (
                || v.tiles[core].proxy.cache[idx].coh.IMAD?
                || v.tiles[core].proxy.cache[idx].coh.SMAD?
              );
            assert false;
          }
        }
      } 
    }
  }

  lemma EnginePerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.NextInstStep?
    requires ProxyAddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L2AddressesUnique(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L2InCohMMeansAddrNotInOtherL2s(c, v)
    requires MInEngineMeansMinL2(c, v)
    requires L2DirectoryInSDAndMInEngineMeansFormerOwner(c, v)
    requires L2DirectoryInMAndMInEngineMeansOwnerOrFwdGetMInFlight(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.MIA?
        || v'.tiles[core].proxy.cache[idx1].coh.MIF?
      )
      && (
        || DirMProxyOwnerL2CacheEntry(c, v', core, idx2)
        || DirSDProxyOwnerL2CacheEntry(c, v', core, idx2)
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      var addr := v.tiles[core].proxy.cache[idx1].addr;
      var inst := step.tile_step.eng_step.inst;
      // dirM/SD means CohML2 for for 
      // assert CohML2CacheEntry(c, v, core, idx2);
      if inst.RMW? || inst.Store? {
        if inst.addr == addr {
          var entry := v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx];
          assert entry.addr == addr;
          assert CohMEL1CacheEntry(c, v, step.tile_idx, step.tile_step.eng_step.c_idx);
          // cohMl1 means its in L2 for this core
          if core != step.tile_idx {
            assert !L2AddrNotInCache(c, v, step.tile_idx, addr);
            var idx: nat :| NonEmptyL2CacheEntry(c, v, step.tile_idx, idx)
              && v.tiles[step.tile_idx].l2.cache[idx].addr == addr;
            assert CohML2CacheEntry(c, v, step.tile_idx, idx);
            assert L2AddrNotInCache(c, v, core, addr);
            // because we aren't in I state, we must have it loadable, a contradiction
            assert !DirIL2CacheEntry(c, v, core, idx2);
            assert v.tiles[core].l2.cache[idx2].coh.Loadable();
            assert false;
          } else {
            // its m or sd with core owner, and we know its not the latter
            assert DirML2CacheEntry(c, v, core, idx2);
            var dst :| FwdGetMInFlight(c, v, addr, Cache(core, Proxy), dst);
            var idx :| NonEmptyProxyCacheEntry(c, v, core, idx)
              && v.tiles[core].proxy.cache[idx].addr == addr
              && (
                || v.tiles[core].proxy.cache[idx].coh.IMAD?
                || v.tiles[core].proxy.cache[idx].coh.SMAD?
              );
            assert false;
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires ProxyAddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L2AddressesUnique(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L2InCohMMeansAddrNotInOtherL2s(c, v)
    requires MInCoreMeansMinL2(c, v)
    requires MInEngineMeansMinL2(c, v)
    requires L2DirectoryInSDAndMInCoreMeansFormerOwner(c, v)
    requires L2DirectoryInSDAndMInEngineMeansFormerOwner(c, v)
    requires L2DirectoryInMAndMInCoreMeansOwnerOrFwdGetMInFlight(c, v)
    requires L2DirectoryInMAndMInEngineMeansOwnerOrFwdGetMInFlight(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {
    if step.tile_step.CoreStep? {
      CorePerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step, re);
    } else {
      assert step.tile_step.EngineStep?;
      EnginePerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v, v', step, re);
    } 
  }

  lemma StartEndCBPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v', core, idx1)
      && NonEmptyL2CacheEntry(c, v', core, idx2)
      && (
        || v'.tiles[core].proxy.cache[idx1].coh.MIA?
        || v'.tiles[core].proxy.cache[idx1].coh.MIF?
      )
      && (
        || DirMProxyOwnerL2CacheEntry(c, v', core, idx2)
        || DirSDProxyOwnerL2CacheEntry(c, v', core, idx2)
      )
      && v'.tiles[core].l2.cache[idx2].addr == v'.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core].proxy.cache[idx1].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx2) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx2) && PrivateMorph(v'.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
    {
      var addr := v'.tiles[core].proxy.cache[idx1].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          }
        }
      } 
    }
  }

  lemma CoreNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma ProxyNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma EngineNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma MemoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L2DirectoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {
    forall core1: nat, idx1: nat, core2: nat, idx2: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core1, idx1)
      && (
        || v'.tiles[core1].l2.cache[idx1].coh.MIA?
        || v'.tiles[core1].l2.cache[idx1].coh.MIF?
      )
      && (
        || (DirML3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.owner == Cache(core1, L2))
        || (DirSDL3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.former_owner == Cache(core1, L2))
      )
      && v'.tiles[core2].l3.cache[idx2].addr == v'.tiles[core1].l2.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core1].l2.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core1].l2.cache[idx1].addr].wcb.Some?
    )
    {
      if step.tile_idx == core1
        // && step.tile_step.l2_step.CacheCommunicationStep?
        && step.tile_step.l2_step.idx == idx1
        && step.tile_step.l2_step.c_step.EvictStep?
        && v.tiles[core1].l2.cache[idx1].coh.M?
      {
        assert v.tiles[core1].l2.cache[idx1].dirty;
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L3RespMemoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {}

  lemma L3DirectoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires L2AddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {
    forall core1: nat, idx1: nat, core2: nat, idx2: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core1, idx1)
      && (
        || v'.tiles[core1].l2.cache[idx1].coh.MIA?
        || v'.tiles[core1].l2.cache[idx1].coh.MIF?
      )
      && (
        || (DirML3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.owner == Cache(core1, L2))
        || (DirSDL3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.former_owner == Cache(core1, L2))
      )
      && v'.tiles[core2].l3.cache[idx2].addr == v'.tiles[core1].l2.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core1].l2.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core1].l2.cache[idx1].addr].wcb.Some?
    )
    {
      if step.tile_idx == core2
        && step.tile_step.l3_step.opt_idx.Some?
        && step.tile_step.l3_step.opt_idx.val == idx2
        && step.tile_step.l3_step.msg.coh_msg.GetM?
        && step.tile_step.l3_step.msg.meta.src == Cache(core1, L2)
      {
        assert GetMInFlight(c, v, v.tiles[core2].l3.cache[idx2].addr, Cache(core1, L2), Cache(core2, L3)) by {
          reveal GetMInFlight;
        }
        var idx: nat :| NonEmptyNonPendingL2CacheEntry(c, v, core1, idx) 
          && v.tiles[core1].l2.cache[idx].addr == v.tiles[core2].l3.cache[idx2].addr
          && (
            || v.tiles[core1].l2.cache[idx].coh.IMAD?
            || v.tiles[core1].l2.cache[idx].coh.SMAD?
          );
      }
    }
  }

  lemma NoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2AddressesUnique(c, v)
    requires GetMInFlightMeansSourceIsTransitioningToM(c, v)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  // need m => not in core etc for engine
  lemma CorePerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.NextInstStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {
    forall core1: nat, idx1: nat, core2: nat, idx2: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core1, idx1)
      && (
        || v'.tiles[core1].l2.cache[idx1].coh.MIA?
        || v'.tiles[core1].l2.cache[idx1].coh.MIF?
      )
      && (
        || (DirML3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.owner == Cache(core1, L2))
        || (DirSDL3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.former_owner == Cache(core1, L2))
      )
      && v'.tiles[core2].l3.cache[idx2].addr == v'.tiles[core1].l2.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core1].l2.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core1].l2.cache[idx1].addr].wcb.Some?
    )
    {
      assert NonEmptyNonPendingL2CacheEntry(c, v, core1, idx1);
      if (DirML3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.owner == Cache(core1, L2)) {
        assert DirML3CacheEntry(c, v, core2, idx2);
      } else {
        assert DirSDL3CacheEntry(c, v, core2, idx2);
      }
    }
  }

  lemma EnginePerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.NextInstStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {
    forall core1: nat, idx1: nat, core2: nat, idx2: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core1, idx1)
      && (
        || v'.tiles[core1].l2.cache[idx1].coh.MIA?
        || v'.tiles[core1].l2.cache[idx1].coh.MIF?
      )
      && (
        || (DirML3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.owner == Cache(core1, L2))
        || (DirSDL3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.former_owner == Cache(core1, L2))
      )
      && v'.tiles[core2].l3.cache[idx2].addr == v'.tiles[core1].l2.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core1].l2.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core1].l2.cache[idx1].addr].wcb.Some?
    )
    {
      assert NonEmptyNonPendingL2CacheEntry(c, v, core1, idx1);
      if (DirML3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.owner == Cache(core1, L2)) {
        assert DirML3CacheEntry(c, v, core2, idx2);
      } else {
        assert DirSDL3CacheEntry(c, v, core2, idx2);
      }
    }
  }

  lemma PerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {
    if step.tile_step.CoreStep? {
      CorePerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step, re);
    }
    if step.tile_step.EngineStep? {
      EnginePerformNextInstPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v, v', step, re);
    }
  }

  lemma StartEndCBPreservesMEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)
    ensures MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v')
  {
    forall core1: nat, idx1: nat, core2: nat, idx2: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core1, idx1)
      && (
        || v'.tiles[core1].l2.cache[idx1].coh.MIA?
        || v'.tiles[core1].l2.cache[idx1].coh.MIF?
      )
      && (
        || (DirML3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.owner == Cache(core1, L2))
        || (DirSDL3CacheEntry(c, v', core2, idx2) && v'.tiles[core2].l3.cache[idx2].dir.former_owner == Cache(core1, L2))
      )
      && v'.tiles[core2].l3.cache[idx2].addr == v'.tiles[core1].l2.cache[idx1].addr
      && AddrIsInEpoch(c, v', v'.tiles[core1].l2.cache[idx1].addr)
    )
    ensures (
      && v'.g.callback_epochs[v'.tiles[core1].l2.cache[idx1].addr].wcb.Some?
    )
    {
      var addr := v'.tiles[core1].l2.cache[idx1].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert SharedMorph(addr);
          assert !L3AddrNotInCache(c, v, c.addr_map(addr), addr);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert SharedMorph(addr);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          assert SharedMorph(addr);
          reveal L3PendingCallbackForAddr;
          assert v.tiles[c.addr_map(addr)].l3.cache[other_idx].addr == addr;
          assert false;
        }
      } 
    }
  }

  lemma CoreNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      if !DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) {
        reveal DataInFlight;
        assert step.msgOps.recv.val.coh_msg.FwdGetM? || step.msgOps.recv.val.coh_msg.FwdGetS?;
        assert step.msgOps.recv.val.meta.src == Cache(core, Proxy);
        assert v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].dirty;
        if step.msgOps.recv.val.coh_msg.FwdGetM? {
          assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, step.msgOps.recv.val.meta.src, Cache(core, L1)) by {
            reveal FwdGetMInFlight;
            assert step.msgOps.recv.val.coh_msg.FwdGetM?;
          }
        } else {
          assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, step.msgOps.recv.val.meta.src, Cache(core, L1)) by {
            reveal FwdGetSInFlight;
            assert step.msgOps.recv.val.coh_msg.FwdGetS?;
          }
        }
        if v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.M? {
          assert v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?;
        } else {
          assert v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.MIA? 
            || v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.MIF?;
          assert v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?;
        }
        assert DirtyL2CacheEntry(c, v, core, idx);
      }
    }
  }

  lemma EngineNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      if !DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) {
        reveal DataInFlight;
        assert step.msgOps.recv.val.coh_msg.FwdGetM? || step.msgOps.recv.val.coh_msg.FwdGetS?;
        assert step.msgOps.recv.val.meta.src == Cache(core, Proxy);
        assert v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].dirty;
        if step.msgOps.recv.val.coh_msg.FwdGetM? {
          assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, step.msgOps.recv.val.meta.src, Cache(core, eL1)) by {
            reveal FwdGetMInFlight;
            assert step.msgOps.recv.val.coh_msg.FwdGetM?;
          }
        } else {
          assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, step.msgOps.recv.val.meta.src, Cache(core, eL1)) by {
            reveal FwdGetSInFlight;
            assert step.msgOps.recv.val.coh_msg.FwdGetS?;
          }
        }
        if v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.M? {
          assert v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?;
        } else {
          assert v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.MIA? 
            || v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.MIF?;
          assert v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?;
        }
        assert DirtyL2CacheEntry(c, v, core, idx);
      }
    }
  }

  lemma ProxyNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires ProxyAddressesUnique(c, v)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires FwdGetSInFlightToT1MeansSourceIsTransitioningToS(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      // won't be receiving a fwdgetm/s to proxy from proxy
      if !DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) {
        reveal DataInFlight;
        assert step.msgOps.recv.val.coh_msg.FwdGetM? || step.msgOps.recv.val.coh_msg.FwdGetS?;
        assert step.msgOps.recv.val.meta.src == Cache(core, Proxy);
        if step.msgOps.recv.val.coh_msg.FwdGetM? {
          assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, Proxy)) by {
            reveal FwdGetMInFlight;
            assert step.msgOps.recv.val.coh_msg.FwdGetM?;
          }
        } else {
          assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, Proxy)) by {
            reveal FwdGetSInFlight;
            assert step.msgOps.recv.val.coh_msg.FwdGetS?;
          }
        }
        assert false;
      }
    }
  }
  
  lemma L2DirectoryMessageNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2QueueHeadsWellformed(c, v)
    requires L2AddressesUnique(c, v)
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    requires NoGetSAndReturningData(c, v)
    requires NoGetMAndReturningData(c, v)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      var addr := v'.tiles[core].l2.cache[idx].addr;
      assert NonEmptyL2CacheEntry(c, v, core, idx);
      if !DataInFlight(c, v, addr, src, Cache(core, Proxy), val) {
        reveal DataInFlight;
        assert step.tile_idx == core;
        assert step.tile_step.l2_step.opt_idx == Some(idx);
        assert DirIL2CacheEntry(c, v, core, idx) || DirSL2CacheEntry(c, v, core, idx);
      } else if step.tile_idx == core && 
        step.tile_step.l2_step.opt_idx.Some? &&
        step.tile_step.l2_step.opt_idx.val == idx {
        assert DataInFlight(c, v, addr, src, Cache(core, Proxy), val);
        if step.tile_step.l2_step.msg.coh_msg.GetM? 
          && step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy) {
          assert GetMInFlight(c, v, addr, Cache(core, Proxy), Cache(core, L2)) by {
            reveal GetMInFlight;
          }
          assert false;
        } else if step.tile_step.l2_step.msg.coh_msg.GetS? 
          && step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy) {
          assert GetSInFlight(c, v, addr, Cache(core, Proxy), Cache(core, L2)) by {
            reveal GetSInFlight;
          }
          assert false;
        } else if step.tile_step.l2_step.msg.coh_msg.PutM? {
          if v.tiles[core].l2.cache[idx].dir.M? 
            && v.tiles[core].l2.cache[idx].dir.owner == step.tile_step.l2_step.msg.meta.src 
            && v.tiles[core].l2.cache[idx].dir.owner.Cache? && !v.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
          {
            assert PutMInFlight(c, v, addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
              reveal PutMInFlight;
            }
          } 
        } else if step.tile_step.l2_step.msg.coh_msg.Data? {
          assert v.tiles[core].l2.cache[idx].dir.SD?;
          assert DataInFlight(c, v, addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
            reveal DataInFlight;
          }
        }
        // step.tile_step.l2_step.msg.coh_msg.GetM? &&
        // step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy) {
        // this is a GetM, so we know that the data in flight is not a writeback
        // and thus the dirty bit should not be set
        // assert !DirtyL2CacheEntry(c, v', core, idx);
      } 
      // else {
      //   // otherwise we are in a state where we have data in flight to proxy
      //   // and thus the dirty bit should be set
      //   assert DirtyL2CacheEntry(c, v', core, idx);
      // }
      // need that fwd can't be at same time as data
    }
  }
  
  lemma L2ScheduleCallbackNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) by {
        reveal DataInFlight;
      }
      assert NonEmptyL2CacheEntry(c, v, core, idx);
    }
  }

  lemma L2CacheCommunicationNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires L2QueueHeadsWellformed(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) by {
        reveal DataInFlight;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) by {
        reveal DataInFlight;
      }
      assert NonEmptyL2CacheEntry(c, v, core, idx);
      if step.tile_idx == core && step.tile_step.l2_step.eng_resp.idx == idx 
      {
        assert IsInFlightOnMissResponse(c, v, v.tiles[core].l2.cache[idx].addr, step.msgOps.recv.val, idx);
      }
    }
  }

  lemma L3NoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires L3QueueHeadsWellformed(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) by {
        reveal DataInFlight;
      }
      assert NonEmptyL2CacheEntry(c, v, core, idx);
    }
  }

  lemma MemoryNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires MemMessagesWellformed(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) by {
        reveal DataInFlight;
      }
      assert NonEmptyL2CacheEntry(c, v, core, idx);
    }
  }

  lemma NoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires DirtyMorphAddressMeansInterveningWriteCore(c, v)
    requires DirtyMorphAddressMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v)
    requires MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v)
    requires MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v)
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    requires ProxyAddressesUnique(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires FwdGetSInFlightToT1MeansSourceIsTransitioningToS(c, v)
    requires L2AddressesUnique(c, v)
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    requires NoGetSAndReturningData(c, v)
    requires NoGetMAndReturningData(c, v)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires MemMessagesWellformed(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    match step {
      case TileStep(_,tile_step,_) =>
        match tile_step {
          case CoreStep(core_step) => {
            CoreNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
          case L2Step(l2_step) =>
            match l2_step {
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryMessageNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
              }
            }
          case L3Step(_) => {
            L3NoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
          }
        }
      case MemoryStep(_) => {
        MemoryNoOpPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L1InCohMMeansNoT1DataInFlight(c, v)
    requires EL1InCohMMeansNoT1DataInFlight(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) by {
        reveal DataInFlight;
      }
      assert NonEmptyL2CacheEntry(c, v, core, idx);
      var addr := v'.tiles[core].l2.cache[idx].addr;
      var inst := if step.tile_step.CoreStep? then step.tile_step.core_step.inst else step.tile_step.eng_step.inst;
      if inst.RMW? || inst.Store? {
        if inst.addr == addr {
          if step.tile_step.CoreStep? {
            var entry := v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx];
            assert entry.addr == addr;
            assert CohML1CacheEntry(c, v, step.tile_idx, step.tile_step.core_step.idx);
            assert false; // the core can't be taking a step when we have the most recent data in flight to proxy
          } else {
            var entry := v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx];
            assert entry.addr == addr;
            assert CohMEL1CacheEntry(c, v, step.tile_idx, step.tile_step.eng_step.c_idx);
            assert false; // the engine can't be taking a step when we have the most recent data in flight to proxy
          }
        }
      } 
    }
  }
  lemma StartEndCBPreservesDataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    ensures DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v')
  {
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && DataInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures (
      && (DirtyL2CacheEntry(c, v', core, idx) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)) ==> (
        && v'.g.callback_epochs[v'.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
    {
      assert DataInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) by {
        reveal DataInFlight;
      }
      var other_idx: nat :| (
        && NonEmptyNonPendingL2CacheEntry(c, v, core, other_idx) 
        && v.tiles[core].l2.cache[other_idx].addr == v'.tiles[core].l2.cache[idx].addr
        && v.tiles[core].l2.cache[other_idx].coh.Loadable()
        && !DirIL2CacheEntry(c, v, core, other_idx) // not in I
      );
      assert other_idx == idx;
      assert NonEmptyL2CacheEntry(c, v, core, idx);
      var addr := v'.tiles[core].l2.cache[idx].addr;
      if addr == v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr {
        if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnEvictInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else if re == StartOnWriteback || re == EndOnWriteback {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          assert OnWritebackInProgress(c, v, addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.val);
          assert false;
        } else {
          assert re == StartOnMiss || re == EndOnMiss;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          reveal CallbackPresent;
          var other_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
          assert OnMissInProgress(c, v, addr, other_idx);
          if PrivateMorph(addr) {
            reveal L2PendingCallbackForAddr;
            assert false;
          } else {
            assert SharedMorph(addr);
            reveal L3PendingCallbackForAddr;
            assert L3AddrNotInCache(c, v, c.addr_map(addr), addr);
            assert L2AddrNotInCache(c, v, core, addr);
            assert false;
          }
        }
      } 
    }
  }

  lemma MemoryNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma CoreNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma ProxyNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma EngineNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma L3NoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires L3QueueHeadsWellformed(c, v)
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires L2AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires FwdGetSInFlightMeansSrcDstDifferent(c, v)
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
        && dst.core == core 
        && dst.level.Tier1()
        && !dst.level.Proxy?
      by {
        reveal FwdGetSInFlight;
      }
      if core == step.tile_idx 
        && step.tile_step.l2_step.idx == idx 
        {
        var other_idx: nat :| DirSDL2CacheEntry(c, v, core, other_idx)
          && v.tiles[core].l2.cache[other_idx].addr == v.tiles[core].l2.cache[idx].addr
          && v.tiles[core].l2.cache[other_idx].dir.former_owner == dst;
        assert other_idx == idx;
        assert CohML2CacheEntry(c, v, core, idx);
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires L2AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
        && dst.core == core 
        && dst.level.Tier1() 
      by {
        reveal FwdGetSInFlight;
      }
      if core == step.tile_idx && step.tile_step.l2_step.eng_resp.idx == idx {
        assert IsInFlightOnMissResponse(c, v, v.tiles[core].l2.cache[idx].addr, step.msgOps.recv.val, idx);
        assert InFlightEngineResponse(c, v, step.msgOps.recv.val);
        assert InFlightOnMissResponse(c, v, v.tiles[core].l2.cache[idx].addr, idx) by {
          reveal InFlightOnMissResponse;
        }
        assert OnMissInProgress(c, v, v.tiles[core].l2.cache[idx].addr, idx);
        assert PrivateMorph(v.tiles[core].l2.cache[idx].addr);
        reveal L2PendingCallbackForAddr;
        // can't have a fwdgetS in flight if we are receiving the most recent data from engine
        var other_idx: nat :| DirSDL2CacheEntry(c, v, core, other_idx)
            && v.tiles[core].l2.cache[other_idx].addr == v.tiles[core].l2.cache[idx].addr
            && v.tiles[core].l2.cache[other_idx].dir.former_owner == dst;
        // assert other_idx == idx;
        assert false; 
      }
    }
  }

  lemma L2DirectoryNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      if !FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) {
        reveal FwdGetSInFlight;
        assert step.tile_step.l2_step.msg.coh_msg.GetS?;
        assert step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy);
        assert step.tile_idx == core;
        // assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.M?;
        // assume false;
      }
    }
  }

  lemma NoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires FwdGetSInFlightToT1MeansSourceIsTransitioningToS(c, v)
    requires FwdGetSInFlightMeansSrcDstDifferent(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
          }
          case L2Step(l2_step) =>
            match l2_step {
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
            }
          case L3Step(_) => {
            L3NoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetSInFlight;
      }
    }
  }

  lemma StartEndCBPreservesFwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires FwdGetSInFlightMeansDirectoryIsSD(c, v)
    requires FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetSInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetSInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
        && dst.core == core 
        && dst.level.Tier1() 
      by {
        reveal FwdGetSInFlight;
      }
      var other_idx: nat :| DirSDL2CacheEntry(c, v, core, other_idx)
          && v.tiles[core].l2.cache[other_idx].addr == v.tiles[core].l2.cache[idx].addr
          && v.tiles[core].l2.cache[other_idx].dir.former_owner == dst;
      assert other_idx == idx;
      if re == EndOnMiss 
        && v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr == v'.tiles[core].l2.cache[idx].addr 
      {
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].l2.cache[idx].addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
        assert CallbackPresent(c, v , v'.tiles[core].l2.cache[idx].addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type) by {
          reveal CallbackPresent;
        }
        assert OnMissInProgress(c, v, v'.tiles[core].l2.cache[idx].addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx);
        if v'.tiles[core].l2.cache[idx].dirty {
          assert DirtyL2CacheEntry(c, v', core, idx);
        }
        if PrivateMorph(v'.tiles[core].l2.cache[idx].addr) {
          reveal L2PendingCallbackForAddr;
          assert false;
        } else {
          assert SharedMorph(v'.tiles[core].l2.cache[idx].addr);
          reveal L3PendingCallbackForAddr;
          assert L3AddrNotInCache(c, v, c.addr_map(v'.tiles[core].l2.cache[idx].addr), v'.tiles[core].l2.cache[idx].addr);
          assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx].addr);
          assert !DirIL2CacheEntry(c, v, core, idx);
          assert false;
        }
      }
    }
  }

  lemma MemoryNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma CoreNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma ProxyNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma EngineNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma L3NoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires L3QueueHeadsWellformed(c, v)
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires L2AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
        && dst.core == core 
        && dst.level.Tier1()
      by {
        reveal FwdGetMInFlight;
      }
      if core == step.tile_idx 
        && step.tile_step.l2_step.idx == idx 
        {
        var other_idx: nat :| CohML2CacheEntry(c, v, core, other_idx)
          && v.tiles[core].l2.cache[other_idx].addr == v.tiles[core].l2.cache[idx].addr;
        assert other_idx == idx;
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires L2AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
        && dst.core == core 
        && dst.level.Tier1() 
      by {
        reveal FwdGetMInFlight;
      }
      if core == step.tile_idx && step.tile_step.l2_step.eng_resp.idx == idx {
        assert IsInFlightOnMissResponse(c, v, v.tiles[core].l2.cache[idx].addr, step.msgOps.recv.val, idx);
        assert InFlightEngineResponse(c, v, step.msgOps.recv.val);
        assert InFlightOnMissResponse(c, v, v.tiles[core].l2.cache[idx].addr, idx) by {
          reveal InFlightOnMissResponse;
        }
        assert OnMissInProgress(c, v, v.tiles[core].l2.cache[idx].addr, idx);
        assert PrivateMorph(v.tiles[core].l2.cache[idx].addr);
        reveal L2PendingCallbackForAddr;
        // can't have a fwdgetS in flight if we are receiving the most recent data from engine
        var other_idx: nat :|
          (
            || DirML2CacheEntry(c, v, core, other_idx)
            || DirSDL2CacheEntry(c, v, core, other_idx)
          )
          && v.tiles[core].l2.cache[other_idx].addr == v.tiles[core].l2.cache[idx].addr;
        // assert other_idx == idx;
        assert false; 
      }
    }
  }

  lemma L2DirectoryNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      if !FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) {
        reveal FwdGetMInFlight;
        assert step.tile_step.l2_step.msg.coh_msg.GetM?;
        assert step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy);
        assert step.tile_idx == core;
        // assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.opt_idx.val].dir.M?;
        // assume false;
      }
    }
  }

  lemma NoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2AddressesUnique(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires L2DirMorSDMeansL2CohM(c, v)
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
          }
          case L2Step(l2_step) =>
            match l2_step {
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
              }
            }
          case L3Step(_) => {
            L3NoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) by {
        reveal FwdGetMInFlight;
      }
    }
  }

  lemma StartEndCBPreservesFwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2NotDirIMeansLoadableCoh(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v)
    requires FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v')
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && FwdGetMInFlight(c, v', v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
    ) 
    ensures DirtyL2CacheEntry(c, v', core, idx)
    {
      assert FwdGetMInFlight(c, v, v'.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
        && dst.core == core 
        && dst.level.Tier1() 
      by {
        reveal FwdGetMInFlight;
      }
      var other_idx: nat :| CohML2CacheEntry(c, v, core, other_idx)
        && v.tiles[core].l2.cache[other_idx].addr == v.tiles[core].l2.cache[idx].addr;
      assert other_idx == idx;
      if re == EndOnMiss 
        && v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr == v'.tiles[core].l2.cache[idx].addr 
      {
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].l2.cache[idx].addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
        assert CallbackPresent(c, v , v'.tiles[core].l2.cache[idx].addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type) by {
          reveal CallbackPresent;
        }
        assert OnMissInProgress(c, v, v'.tiles[core].l2.cache[idx].addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx);
        if v'.tiles[core].l2.cache[idx].dirty {
          assert DirtyL2CacheEntry(c, v', core, idx);
        }
        if PrivateMorph(v'.tiles[core].l2.cache[idx].addr) {
          reveal L2PendingCallbackForAddr;
          assert false;
        } else {
          assert SharedMorph(v'.tiles[core].l2.cache[idx].addr);
          reveal L3PendingCallbackForAddr;
          assert L3AddrNotInCache(c, v, c.addr_map(v'.tiles[core].l2.cache[idx].addr), v'.tiles[core].l2.cache[idx].addr);
          assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx].addr);
          assert !DirIL2CacheEntry(c, v, core, idx);
          assert false;
        }
      }
    }
  }
}
