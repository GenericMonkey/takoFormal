include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module NetworkDiffCBsProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes

  ///////////////////////////////////////////////////////////////////////////////////
  // EngReqsInNetworkAreDiffThanCurrentCallbacks
  ///////////////////////////////////////////////////////////////////////////////////
  lemma CoreNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {}

  lemma ProxyNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {}

  lemma EngineReceiveCallbackReqNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {}

  lemma EngineNotReceiveCallbackReqNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {
    assert step.tile_step.eng_step.CacheCommunicationStep?;
  }

  lemma EngineNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {
    if step.tile_step.eng_step.ReceiveCallbackReqStep? {
      EngineReceiveCallbackReqNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
    } else {
      EngineNotReceiveCallbackReqNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
    }
  }

  lemma L2NotScheduleCallbackNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires !step.tile_step.l2_step.ScheduleCallbackStep?
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {
    match step.tile_step.l2_step.eng_req {
      case OnMiss(idx) => {
        forall tile: nat, buf : nat, idx: nat | (
          && IsBufferEntry(c, v', tile, buf)
          && InFlightEngineRequest(c, v', v'.tiles[tile].engine.buffer[buf].addr, idx)
        )
        ensures (
          && var msg := v'.network.inFlightEngReqs[v'.tiles[tile].engine.buffer[buf].addr][idx];
          && !(msg.engine_req.OnMiss? && v'.tiles[tile].engine.buffer[buf].cb_type.OnMiss?)
        )
        {
          var msg := v'.network.inFlightEngReqs[v'.tiles[tile].engine.buffer[buf].addr][idx];
          assert IsBufferEntry(c, v, tile, buf);
          if v'.tiles[tile].engine.buffer[buf].addr == step.tile_step.l2_step.addr {

            if !CallbackPresentInBufferLocation(c, v, v'.tiles[tile].engine.buffer[buf].addr, CallbackType.OnMiss, tile, buf)
            {
              assert !(msg.engine_req.OnMiss? && v'.tiles[tile].engine.buffer[buf].cb_type.OnMiss?);
            } else if v'.tiles[tile].engine.buffer[buf].cb_type != step.tile_step.l2_step.eng_req {
              assert CallbackPresent(c, v, v.tiles[tile].engine.buffer[buf].addr, v.tiles[tile].engine.buffer[buf].cb_type) by { reveal CallbackPresent; }
              assert OnMissInProgress(c, v, v.tiles[tile].engine.buffer[buf].addr, v.tiles[tile].engine.buffer[buf].cb_type.idx);
              reveal L2PendingCallbackForAddr;
              assert false;
              assert !(msg.engine_req.OnMiss? && v'.tiles[tile].engine.buffer[buf].cb_type.OnMiss?);
            } else {
              assert CallbackPresent(c, v, v.tiles[tile].engine.buffer[buf].addr, step.tile_step.l2_step.eng_req) by { reveal CallbackPresent; }
              assert OnMissInProgress(c, v, v.tiles[tile].engine.buffer[buf].addr, step.tile_step.l2_step.eng_req.idx);
              reveal L2PendingCallbackForAddr;
              assert false;
            }
          }
        }
        assert EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v');
      }
      case _ => {
        forall tile: nat, buf : nat, idx: nat | (
          && IsBufferEntry(c, v', tile, buf)
          && InFlightEngineRequest(c, v', v'.tiles[tile].engine.buffer[buf].addr, idx)
        )
        ensures (
          && var msg := v'.network.inFlightEngReqs[v.tiles[tile].engine.buffer[buf].addr][idx];
          && !(msg.engine_req.OnEvict? && v'.tiles[tile].engine.buffer[buf].cb_type.OnEvict?)
          && !(msg.engine_req.OnEvict? && v'.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack?)
          && !(msg.engine_req.OnWriteBack? && v.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack?)
          && !(msg.engine_req.OnWriteBack? && v.tiles[tile].engine.buffer[buf].cb_type.OnEvict?)
        )
        {
          reveal CallbackPresent;
          assert IsBufferEntry(c, v, tile, buf);
          if v'.tiles[tile].engine.buffer[buf].cb_type.OnEvict? {
            assert CallbackPresent(c, v, v'.tiles[tile].engine.buffer[buf].addr, EngineRequest.OnEvict(v'.tiles[tile].engine.buffer[buf].cb_type.val));
            assert OnEvictInProgress(c, v, v'.tiles[tile].engine.buffer[buf].addr, v'.tiles[tile].engine.buffer[buf].cb_type.val);
          }
          if v'.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack? {
            assert CallbackPresent(c, v, v'.tiles[tile].engine.buffer[buf].addr, EngineRequest.OnWriteBack(v'.tiles[tile].engine.buffer[buf].cb_type.val));
            assert OnWritebackInProgress(c, v, v'.tiles[tile].engine.buffer[buf].addr, v'.tiles[tile].engine.buffer[buf].cb_type.val);
          }
        }
        assert EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v');
      }
    }
  }

  lemma L2NoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {
    if step.tile_step.l2_step.ScheduleCallbackStep? {
      L2ScheduleCallbackNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
    } else {
      L2NotScheduleCallbackNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
    }
  }


  lemma L3NotScheduleCallbackNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {}

  lemma L3ScheduleCallbackNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {
    match step.tile_step.l3_step.eng_req {
      case OnMiss(idx) => {
        forall tile: nat, buf : nat, idx: nat | (
          && IsBufferEntry(c, v', tile, buf)
          && InFlightEngineRequest(c, v', v'.tiles[tile].engine.buffer[buf].addr, idx)
        )
        ensures (
          && var msg := v'.network.inFlightEngReqs[v'.tiles[tile].engine.buffer[buf].addr][idx];
          && !(msg.engine_req.OnMiss? && v'.tiles[tile].engine.buffer[buf].cb_type.OnMiss?)
        )
        {
          var msg := v'.network.inFlightEngReqs[v'.tiles[tile].engine.buffer[buf].addr][idx];
          assert IsBufferEntry(c, v, tile, buf);
          if v'.tiles[tile].engine.buffer[buf].addr == step.tile_step.l3_step.addr {

            if !CallbackPresentInBufferLocation(c, v, v'.tiles[tile].engine.buffer[buf].addr, CallbackType.OnMiss, tile, buf)
            {
              assert !(msg.engine_req.OnMiss? && v'.tiles[tile].engine.buffer[buf].cb_type.OnMiss?);
            } else if v'.tiles[tile].engine.buffer[buf].cb_type != step.tile_step.l3_step.eng_req {
              assert CallbackPresent(c, v, v.tiles[tile].engine.buffer[buf].addr, v.tiles[tile].engine.buffer[buf].cb_type) by { reveal CallbackPresent; }
              assert OnMissInProgress(c, v, v.tiles[tile].engine.buffer[buf].addr, v.tiles[tile].engine.buffer[buf].cb_type.idx);
              reveal L3PendingCallbackForAddr;
              assert false;
              assert !(msg.engine_req.OnMiss? && v'.tiles[tile].engine.buffer[buf].cb_type.OnMiss?);
            } else {
              assert CallbackPresent(c, v, v.tiles[tile].engine.buffer[buf].addr, step.tile_step.l3_step.eng_req) by { reveal CallbackPresent; }
              assert OnMissInProgress(c, v, v.tiles[tile].engine.buffer[buf].addr, step.tile_step.l3_step.eng_req.idx);
              reveal L3PendingCallbackForAddr;
              assert false;
            }
          }
        }
        assert EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v');
      }
      case _ => {
        forall tile: nat, buf : nat, idx: nat | (
          && IsBufferEntry(c, v', tile, buf)
          && InFlightEngineRequest(c, v', v'.tiles[tile].engine.buffer[buf].addr, idx)
        )
        ensures (
          && var msg := v'.network.inFlightEngReqs[v'.tiles[tile].engine.buffer[buf].addr][idx];
          && !(msg.engine_req.OnEvict? && v'.tiles[tile].engine.buffer[buf].cb_type.OnEvict?)
          && !(msg.engine_req.OnEvict? && v'.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack?)
          && !(msg.engine_req.OnWriteBack? && v'.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack?)
          && !(msg.engine_req.OnWriteBack? && v'.tiles[tile].engine.buffer[buf].cb_type.OnEvict?)
        )
        {
          reveal CallbackPresent;
          assert IsBufferEntry(c, v, tile, buf);
          if v'.tiles[tile].engine.buffer[buf].cb_type.OnEvict? {
            assert CallbackPresent(c, v, v'.tiles[tile].engine.buffer[buf].addr, EngineRequest.OnEvict(v'.tiles[tile].engine.buffer[buf].cb_type.val));
            assert OnEvictInProgress(c, v, v'.tiles[tile].engine.buffer[buf].addr, v'.tiles[tile].engine.buffer[buf].cb_type.val);
          }
          if v'.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack? {
            assert CallbackPresent(c, v, v'.tiles[tile].engine.buffer[buf].addr, EngineRequest.OnWriteBack(v'.tiles[tile].engine.buffer[buf].cb_type.val));
            assert OnWritebackInProgress(c, v, v'.tiles[tile].engine.buffer[buf].addr, v'.tiles[tile].engine.buffer[buf].cb_type.val);
          }
        }
        assert EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v');
      }
    }
  }

  lemma L3NoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {
    if step.tile_step.l3_step.ScheduleCallbackStep? {
      L3ScheduleCallbackNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
    } else {
      L3NotScheduleCallbackNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
    }
  }

  lemma NoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        assert EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v');
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {}

  lemma StartEndCBPreservesEngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v')
  {
    forall tile: nat, buf : nat, idx: nat | (
      && IsBufferEntry(c, v', tile, buf) 
      && InFlightEngineRequest(c, v', v'.tiles[tile].engine.buffer[buf].addr, idx) 
    ) 
    ensures (
      && var msg := v'.network.inFlightEngReqs[v'.tiles[tile].engine.buffer[buf].addr][idx];
      && !(msg.engine_req.OnMiss? && v'.tiles[tile].engine.buffer[buf].cb_type.OnMiss?)
      && !(msg.engine_req.OnEvict? && v'.tiles[tile].engine.buffer[buf].cb_type.OnEvict?)
      && !(msg.engine_req.OnEvict? && v'.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack?)
      && !(msg.engine_req.OnWriteBack? && v'.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack?)
      && !(msg.engine_req.OnWriteBack? && v'.tiles[tile].engine.buffer[buf].cb_type.OnEvict?)
    ) {
      assert IsBufferEntry(c, v, tile, buf);
      assert InFlightEngineRequest(c, v, v'.tiles[tile].engine.buffer[buf].addr, idx);
    }
  }
}