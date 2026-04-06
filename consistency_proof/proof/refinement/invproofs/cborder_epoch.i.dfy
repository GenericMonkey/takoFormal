include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module CBOrderTrackerEpochProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes

  lemma EngineReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0)
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].Out?
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) ==> v'.g.callback_epochs[addr].Miss?)
        )
      )
    )
    {
      var buf := v'.tiles[tile].engine.cb_order[addr][0];
      var msg := step.msgOps.recv.val;
      if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) {
        if IsUnstartedBufferEntry(c, v', tile, buf) {
          if !IsUnstartedBufferEntry(c, v, tile, buf) {
            assert addr == step.msgOps.recv.val.meta.addr;
            assert tile == step.tile_idx;
            assert buf == step.tile_step.eng_step.idx;
            assert IsInFlightOnMissRequest(c, v, addr, 0, msg.engine_req.idx);
            assert InFlightOnMissRequest(c, v, addr, msg.engine_req.idx) by { reveal InFlightOnMissRequest; }
            assert !(addr in v.tiles[tile].engine.cb_order) || |v.tiles[tile].engine.cb_order[addr]| == 0 by {
              if addr in v.tiles[tile].engine.cb_order && |v.tiles[tile].engine.cb_order[addr]| > 0 {
                var idx := v.tiles[tile].engine.cb_order[addr][0];
                assert AddrInTileCBOrderTracker(c, v, addr, tile);
                assert idx in v.tiles[tile].engine.cb_order[addr];
                assert false;
              }
            }
            forall val : Value
              ensures !OnEvictInProgress(c, v, addr, val)
              ensures !OnWritebackInProgress(c, v, addr, val)
            {
              assert !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by {
                reveal CallbackPresent;
                if t: nat, b: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, t, b) && v.tiles[t].engine.buffer[b].cb_type == EngineRequest.OnEvict(val) {
                  assert t == tile;
                  assert AddrInTileCBOrderTracker(c, v, addr, t);
                  assert b in v.tiles[tile].engine.cb_order[addr];
                  assert false;
                }
              }
              assert !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by {
                reveal CallbackPresent;
                if t: nat, b: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, t, b) && v.tiles[t].engine.buffer[b].cb_type == EngineRequest.OnWriteBack(val) {
                  assert t == tile;
                  assert AddrInTileCBOrderTracker(c, v, addr, t);
                  assert b in v.tiles[tile].engine.cb_order[addr];
                  assert false;
                }
              }
            }
            assert OnMissInProgress(c, v, addr, msg.engine_req.idx);
            if PrivateMorph(addr) {
              reveal L2PendingCallbackForAddr;
            } else {
              assert SharedMorph(addr);
              reveal L3PendingCallbackForAddr;
            }
            assert v.g.callback_epochs[addr].Out?;
            assert v'.g.callback_epochs[addr].Out?;
          }
        }
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {
    assert step.tile_step.eng_step.CacheCommunicationStep?;
  }

  lemma MemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma CoreNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma ProxyNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L2DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L3ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L3DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L3ReqMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L3RespMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L3ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma L3ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {}

  lemma NoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
            }
          }
          case CoreStep(_) => {
            CoreNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerMiss(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0)
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].Out?
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) ==> v'.g.callback_epochs[addr].Miss?)
        )
      )
    )
    {
      var buf := v'.tiles[tile].engine.cb_order[addr][0];
      var step_entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      assert CBOrderTrackerValidIndex(c, v, addr, tile, 0);
      if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) {
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        if IsUnstartedBufferEntry(c, v', tile, buf) {
          assert IsUnstartedBufferEntry(c, v, tile, buf);
          if addr == step_entry.addr {
            assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(step_entry.cb_type), step.tile_idx, step.tile_step.eng_step.idx);
            assert step_entry.cb_type.OnEvict? || step_entry.cb_type.OnWriteBack?;
            assert v'.g.callback_epochs[addr].Out?;
          } 
        }
        if CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) {
          if CallbackRunningInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf) {
            if addr == step_entry.addr {
              assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(step_entry.cb_type), step.tile_idx, step.tile_step.eng_step.idx);
              assert false;
            }
            assert v'.g.callback_epochs[addr].Miss?;
          } 
          assert v'.g.callback_epochs[addr].Miss?;
        }
      }
    }
  }

  lemma PerformNextInstPreservesEpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EpochsConsistentWithCBOrderTrackerMiss(c, v)
    ensures EpochsConsistentWithCBOrderTrackerMiss(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0)
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].Out?
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf) ==> v'.g.callback_epochs[addr].Miss?)
        )
      )
    )
    {
      assert CBOrderTrackerValidIndex(c, v, addr, tile, 0);
    }
  }

  
  lemma EngineReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0)
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].In?
            && v'.g.callback_epochs[addr].wcb.None? // some if callback type is onevict
            && MatchesLastWriteMorph(c, v', addr, v'.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==> v'.g.callback_epochs[addr].Evict?)
        )
      )
    )
    {
      var buf := v'.tiles[tile].engine.cb_order[addr][0];
      var msg := step.msgOps.recv.val;
      if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) {
        if IsUnstartedBufferEntry(c, v', tile, buf) {
          if !IsUnstartedBufferEntry(c, v, tile, buf) {
            assert addr == step.msgOps.recv.val.meta.addr;
            assert tile == step.tile_idx;
            assert buf == step.tile_step.eng_step.idx;
            var val := step.msgOps.recv.val.engine_req.val;
            assert IsInFlightOnEvictRequest(c, v, addr, 0, val);
            assert InFlightOnEvictRequest(c, v, addr, val) by { reveal InFlightOnEvictRequest; }
            assert InFlightOnEvictRequestForAddr(c, v, addr) by { reveal InFlightOnEvictRequestForAddr; }
            assert v.g.callback_epochs[addr].In?;
          }
        }
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {
    assert step.tile_step.eng_step.CacheCommunicationStep?;
  }

  lemma MemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma CoreNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma ProxyNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0)
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].In?
            && v'.g.callback_epochs[addr].wcb.None?
            && MatchesLastWriteMorph(c, v', addr, v'.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==> v'.g.callback_epochs[addr].Evict?)
        )
      )
    )
    {}
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma L2DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0)
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].In?
            && v'.g.callback_epochs[addr].wcb.None?
            && MatchesLastWriteMorph(c, v', addr, v'.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==> v'.g.callback_epochs[addr].Evict?)
        )
      )
    )
    {}
  }

  lemma L2ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma L3ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma L3DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma L3ReqMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma L3RespMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma L3ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma L3ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {}

  lemma NoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
            }
          }
          case CoreStep(_) => {
            CoreNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerEvict(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0)
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].In?
            && v'.g.callback_epochs[addr].wcb.None?
            && MatchesLastWriteMorph(c, v', addr, v'.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==> v'.g.callback_epochs[addr].Evict?)
        )
      )
    )
    {
      var buf := v'.tiles[tile].engine.cb_order[addr][0];
      var step_entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      assert CBOrderTrackerValidIndex(c, v, addr, tile, 0);
      if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) {
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
        if IsUnstartedBufferEntry(c, v', tile, buf) {
          assert IsUnstartedBufferEntry(c, v, tile, buf);
          if addr == step_entry.addr {
            assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(step_entry.cb_type), step.tile_idx, step.tile_step.eng_step.idx);
            assert step_entry.cb_type.OnMiss?;
            assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, step_entry.cb_type);
            assert !OnEvictInProgress(c, v, addr, v.tiles[tile].engine.buffer[buf].cb_type.val);
            assert false by {
              reveal CallbackPresent;
            }
          } 
        }
        if CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) {
          if CallbackRunningInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) {
            if addr == step_entry.addr {
              assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(step_entry.cb_type), step.tile_idx, step.tile_step.eng_step.idx);
              assert false;
            }
            assert v'.g.callback_epochs[addr].Evict?;
          } 
          assert v'.g.callback_epochs[addr].Evict?;
        }
      }
    }
  }

  lemma PerformNextInstPreservesEpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EpochsConsistentWithCBOrderTrackerEvict(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures EpochsConsistentWithCBOrderTrackerEvict(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0) 
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].In?
            && v'.g.callback_epochs[addr].wcb.None? // some if callback type is onevict
            && MatchesLastWriteMorph(c, v', addr, v'.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) ==> v'.g.callback_epochs[addr].Evict?)
        )
      )
    )
    {
      assert CBOrderTrackerValidIndex(c, v, addr, tile, 0);
      var buf := v'.tiles[tile].engine.cb_order[addr][0];
      if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf) {
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
        var val := v'.tiles[tile].engine.buffer[buf].cb_type.val;
        assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val)) by { reveal CallbackPresent; }
        assert OnEvictInProgress(c, v, addr, val);
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0)
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].In?
            && v'.g.callback_epochs[addr].wcb.Some?
            && MatchesLastWriteMorph(c, v', addr, v'.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) ==> v'.g.callback_epochs[addr].Evict?)
        )
      )
    )
    {
      var buf := v'.tiles[tile].engine.cb_order[addr][0];
      var msg := step.msgOps.recv.val;
      if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) {
        if IsUnstartedBufferEntry(c, v', tile, buf) {
          if !IsUnstartedBufferEntry(c, v, tile, buf) {
            assert addr == step.msgOps.recv.val.meta.addr;
            assert tile == step.tile_idx;
            assert buf == step.tile_step.eng_step.idx;
            var val := step.msgOps.recv.val.engine_req.val;
            assert IsInFlightOnWritebackRequest(c, v, addr, 0, val);
            assert InFlightOnWritebackRequest(c, v, addr, val) by { reveal InFlightOnWritebackRequest; }
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by { reveal InFlightOnWritebackRequestForAddr; }
            assert v.g.callback_epochs[addr].In?;
          }
        }
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {
    assert step.tile_step.eng_step.CacheCommunicationStep?;
  }

  lemma MemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma CoreNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma ProxyNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L2DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0) 
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].In?
            && v'.g.callback_epochs[addr].wcb.Some?
            && MatchesLastWriteMorph(c, v', addr, v'.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) ==> v'.g.callback_epochs[addr].Evict?)
        )
      )
    )
    {}
  }

  lemma L2ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L3ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L3DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L3ReqMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L3RespMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L3ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma L3ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {}

  lemma NoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires MorphWorkingSetInEpochs(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
            }
          }
          case CoreStep(_) => {
            CoreNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesEpochsConsistentWithCBOrderTrackerWriteback(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    requires OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0)
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].In?
            && v'.g.callback_epochs[addr].wcb.Some?
            && MatchesLastWriteMorph(c, v', addr, v'.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) ==> v'.g.callback_epochs[addr].Evict?)
        )
      )
    )
    {
      var buf := v'.tiles[tile].engine.cb_order[addr][0];
      var step_entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      assert CBOrderTrackerValidIndex(c, v, addr, tile, 0);
      if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) {
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
        if IsUnstartedBufferEntry(c, v', tile, buf) {
          assert IsUnstartedBufferEntry(c, v, tile, buf);
          if addr == step_entry.addr {
            assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(step_entry.cb_type), step.tile_idx, step.tile_step.eng_step.idx);
            assert step_entry.cb_type.OnMiss?;
            assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, step_entry.cb_type);
            assert !OnWritebackInProgress(c, v, addr, v.tiles[tile].engine.buffer[buf].cb_type.val);
            assert false by {
              reveal CallbackPresent;
            }
          } 
        }
        if CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) {
          if CallbackRunningInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) {
            if addr == step_entry.addr {
              assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(step_entry.cb_type), step.tile_idx, step.tile_step.eng_step.idx);
              assert false;
            }
            assert v'.g.callback_epochs[addr].Evict?;
          } 
          assert v'.g.callback_epochs[addr].Evict?;
        }
      }
    }
  }

  lemma PerformNextInstPreservesEpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EpochsConsistentWithCBOrderTrackerWriteback(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    ensures EpochsConsistentWithCBOrderTrackerWriteback(c, v')
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v', addr, tile, 0) 
    ensures (
      && addr in v'.g.callback_epochs
      && var buf := v'.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v', tile, buf) ==> (
            && v'.g.callback_epochs[addr].In?
            && v'.g.callback_epochs[addr].wcb.Some?
            && MatchesLastWriteMorph(c, v', addr, v'.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) ==> v'.g.callback_epochs[addr].Evict?)
        )
      )
    )
    {
      assert CBOrderTrackerValidIndex(c, v, addr, tile, 0);
      var buf := v'.tiles[tile].engine.cb_order[addr][0];
      if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf) {
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
        var val := v'.tiles[tile].engine.buffer[buf].cb_type.val;
        assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val)) by { reveal CallbackPresent; }
        assert OnWritebackInProgress(c, v, addr, val);
      }
    }
  }
}