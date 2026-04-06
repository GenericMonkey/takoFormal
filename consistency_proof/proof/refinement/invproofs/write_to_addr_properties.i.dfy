include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module WritesToAddrProofs {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma NoOpPreservesAddrInEpochMeansEventsWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AddrInEpochMeansEventsWellformed(c, v)
    ensures AddrInEpochMeansEventsWellformed(c, v')
  {}

  lemma StartEndCBPreservesAddrInEpochMeansEventsWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AddrInEpochMeansEventsWellformed(c, v)
    ensures AddrInEpochMeansEventsWellformed(c, v')
  {}
  
  lemma PerformNextInstPreservesAddrInEpochMeansEventsWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AddrInEpochMeansEventsWellformed(c, v)
    ensures AddrInEpochMeansEventsWellformed(c, v')
  {}

  lemma NoOpPreservesAddrInEpochMeansEventsMatchAddrAtomicity(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AddrInEpochMeansEventsMatchAddrAtomicity(c, v)
    ensures AddrInEpochMeansEventsMatchAddrAtomicity(c, v')
  {}

  lemma StartEndCBPreservesAddrInEpochMeansEventsMatchAddrAtomicity(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AddrInEpochMeansEventsMatchAddrAtomicity(c, v)
    ensures AddrInEpochMeansEventsMatchAddrAtomicity(c, v')
  {}

  lemma PerformNextInstPreservesAddrInEpochMeansEventsMatchAddrAtomicity(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires AddrInEpochMeansEventsMatchAddrAtomicity(c, v)
    ensures AddrInEpochMeansEventsMatchAddrAtomicity(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma NoOpPreservesWritesToAddrWellFormed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires WritesToAddrWellFormed(c, v)
    ensures WritesToAddrWellFormed(c, v')
  {}

  lemma StartEndCBPreservesWritesToAddrWellFormed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires WritesToAddrWellFormed(c, v)
    ensures WritesToAddrWellFormed(c, v')
  {}

  lemma PerformNextInstPreservesWritesToAddrWellFormed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires WritesToAddrWellFormed(c, v)
    ensures WritesToAddrWellFormed(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma NoOpPreservesAllWritesInWritesToAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AllWritesInWritesToAddr(c, v)
    ensures AllWritesInWritesToAddr(c, v')
  {}

  lemma StartEndCBPreservesAllWritesInWritesToAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllWritesInWritesToAddr(c, v)
    ensures AllWritesInWritesToAddr(c, v')
  {}
  
  lemma PerformNextInstPreservesAllWritesInWritesToAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllWritesInWritesToAddr(c, v)
    ensures AllWritesInWritesToAddr(c, v')
  {}

  lemma NoOpPreservesMoDeterminedByWritesToAddrOrder(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires MoDeterminedByWritesToAddrOrder(c, v)
    ensures MoDeterminedByWritesToAddrOrder(c, v')
  {}

  lemma StartEndCBPreservesMoDeterminedByWritesToAddrOrder(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires MoDeterminedByWritesToAddrOrder(c, v)
    ensures MoDeterminedByWritesToAddrOrder(c, v')
  {}
  
  lemma PerformNextInstPreservesMoDeterminedByWritesToAddrOrder(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires WritesToAddrWellFormed(c, v)
    requires AllWritesInWritesToAddr(c, v)
    requires AllMoInWritesToAddr(c, v)
    requires AllWritesToAddrLessThanCurrentPCCore(c, v)
    requires AllWritesToAddrLessThanCurrentPCEngine(c, v)
    requires RunningCallbackValuesAgree(c, v)
    requires MoDeterminedByWritesToAddrOrder(c, v)
    ensures MoDeterminedByWritesToAddrOrder(c, v')
  {
    // forall addr: Address, idx1 : nat, idx2: nat | (
    //   && addr in v'.g.writes_to_addr
    //   && idx1 < |v'.g.writes_to_addr[addr]|
    //   && idx2 < |v'.g.writes_to_addr[addr]|
    //   && (idx1 < idx2)
    // ) 
    // ensures
    //   ((v'.g.writes_to_addr[addr][idx1], v'.g.writes_to_addr[addr][idx2]) in v'.g.execution.wit.mo)
    // {
    //   var inst := if step.tile_step.CoreStep? then step.tile_step.core_step.inst else step.tile_step.eng_step.inst;
    //   if (inst.RMW? || inst.Store?) 
    //     && inst.addr == addr 
    //     && idx2 == |v.g.writes_to_addr[addr]|
    //   {
    //     forall w: Event | w in v.g.execution.WritesToAddr(addr)
    //       ensures (w, v'.g.writes_to_addr[addr][idx2]) in v'.g.execution.wit.mo
    //     {}
    //     assert v'.g.writes_to_addr[addr][idx1] == v.g.writes_to_addr[addr][idx1];
    //     assert v.g.writes_to_addr[addr][idx1] in v.g.execution.WritesToAddr(addr);
    //   } 
    // }

    // need uniqueness (use less_than pc)
    forall addr: Address, idx1 : nat, idx2: nat | (
      && addr in v'.g.writes_to_addr
      && idx1 < |v'.g.writes_to_addr[addr]|
      && idx2 < |v'.g.writes_to_addr[addr]|
      && ((v'.g.writes_to_addr[addr][idx1], v'.g.writes_to_addr[addr][idx2]) in v'.g.execution.wit.mo)
    ) 
    ensures
      (idx1 < idx2)
    {
      var inst := if step.tile_step.CoreStep? then step.tile_step.core_step.inst else step.tile_step.eng_step.inst;
      if (inst.RMW? || inst.Store?) 
        && inst.addr == addr
        && addr.Regular?
      {
        if step.tile_step.EngineStep? {
          var id := CallbackId(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr, EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type), v.g.callback_epochs[v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr].epoch);
          assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx);
          assert CurrentSpecCallbackId(c, v, id);
        }
        var e_idx1 := v'.g.writes_to_addr[addr][idx1];
        var e_idx2 := v'.g.writes_to_addr[addr][idx2];
        var e_last := v'.g.writes_to_addr[addr][|v.g.writes_to_addr[addr]|];
        assert (
          || (e_idx1, e_idx2) in v.g.execution.wit.mo
          || (e_idx1, e_idx2) in (set w_o: Event | w_o in v.g.execution.WritesToAddr(addr) :: (w_o, e_last))
        );
        if (e_idx1, e_idx2) in v.g.execution.wit.mo {
          assert idx1 != |v.g.writes_to_addr[addr]| by {
            // if idx1 == |v.g.writes_to_addr[addr]| {
            //   assert false;
            // }
          }
          assert idx2 != |v.g.writes_to_addr[addr]| by {
            // assume false;
          }
        } else {
          assert (e_idx1, e_idx2) in (set w_o: Event | w_o in v.g.execution.WritesToAddr(addr) :: (w_o, e_last));
          assert e_idx2 == e_last;
        }
        // assert v'.g.writes_to_addr[addr][idx2] != v'.g.writes_to_addr[addr][|v.g.writes_to_addr[addr]|];
        // assert idx1 != idx2 by {
        //   assume false;
        // }
        // if (idx1 == |v.g.writes_to_addr[addr]|) {
        //   // assert !(v.g.writes_to_addr[addr][idx1] in v.g.writes_to_addr[addr]);
        //   assert v'.g.writes_to_addr[addr][idx2] == v.g.writes_to_addr[addr][idx2];
        //   forall idx': nat | idx' < idx2
        //     ensures v.g.writes_to_addr[addr][idx'] != v'.g.writes_to_addr[addr][idx1]
        //   {}
        //   assert v.g.writes_to_addr[addr][idx2] != v'.g.writes_to_addr[addr][idx1];
        //   assert false;
        // } else if (idx2 == |v.g.writes_to_addr[addr]|) {
        //   assume false;
        // } else {
        // } 
      }

    }
  }

  lemma NoOpPreservesAllMoInWritesToAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AllMoInWritesToAddr(c, v)
    ensures AllMoInWritesToAddr(c, v')
  {}

  lemma StartEndCBPreservesAllMoInWritesToAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllMoInWritesToAddr(c, v)
    ensures AllMoInWritesToAddr(c, v')
  {}
  
  lemma PerformNextInstPreservesAllMoInWritesToAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllMoInWritesToAddr(c, v)
    requires AllWritesInWritesToAddr(c, v)
    requires WritesToAddrWellFormed(c, v)
    ensures AllMoInWritesToAddr(c, v')
  {}

  lemma NoOpPreservesAllWritesToAddrLessThanCurrentPCCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AllWritesToAddrLessThanCurrentPCCore(c, v)
    ensures AllWritesToAddrLessThanCurrentPCCore(c, v')
  {}

  lemma StartEndCBPreservesAllWritesToAddrLessThanCurrentPCCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllWritesToAddrLessThanCurrentPCCore(c, v)
    ensures AllWritesToAddrLessThanCurrentPCCore(c, v')
  {}

  lemma PerformNextInstPreservesAllWritesToAddrLessThanCurrentPCCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllWritesToAddrLessThanCurrentPCCore(c, v)
    ensures AllWritesToAddrLessThanCurrentPCCore(c, v')
  {}

  lemma NoOpPreservesAllWritesToAddrLessThanCurrentPCEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AllWritesToAddrLessThanCurrentPCEngine(c, v)
    ensures AllWritesToAddrLessThanCurrentPCEngine(c, v')
  {
    forall addr: Address, idx: nat, id: ThreadId, tile: nat, buf: nat | (
      && addr in v'.g.writes_to_addr
      && idx < |v'.g.writes_to_addr[addr]|
      && CurrentSpecCallbackId(c, v', id)
      && CallbackRunningInBufferLocation(c, v', id.addr, id.cb, tile, buf)
      && v'.g.writes_to_addr[addr][idx].info.id == id
    ) 
    ensures (
      && v'.g.writes_to_addr[addr][idx].info.pc.less_than(
        PC(v'.tiles[tile].engine.buffer[buf].pc, v'.tiles[tile].engine.buffer[buf].count)
      )
    )
    {}
  }

  lemma StartEndCBPreservesAllWritesToAddrLessThanCurrentPCEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires ExistingCallbackIdsHaveCorrectEpoch(c, v)
    requires WritesToAddrHaveValidThreadIds(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)

    requires NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)

    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)

    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)

    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)

    requires UniqueTileForCallbackAddr(c, v)
    requires CurrentCallbackIsRunning(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires AllWritesToAddrLessThanCurrentPCEngine(c, v)
    ensures AllWritesToAddrLessThanCurrentPCEngine(c, v')
  {
    forall addr: Address, idx: nat, id: ThreadId, tile: nat, buf: nat | (
      && addr in v'.g.writes_to_addr
      && idx < |v'.g.writes_to_addr[addr]|
      && CurrentSpecCallbackId(c, v', id)
      && CallbackRunningInBufferLocation(c, v', id.addr, id.cb, tile, buf)
      && v'.g.writes_to_addr[addr][idx].info.id == id
    ) 
    ensures (
      && v'.g.writes_to_addr[addr][idx].info.pc.less_than(
        PC(v'.tiles[tile].engine.buffer[buf].pc, v'.tiles[tile].engine.buffer[buf].count)
      )
    )
    {
      if (re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback)
        && v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr == id.addr
        && EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type) == id.cb
      {
        assert CallbackPresentInBufferLocation(c, v, id.addr, id.cb, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx);
        assert tile == step.tile_idx;
        assert buf == step.tile_step.eng_step.idx;
        if CurrentSpecCallbackId(c, v, id) {
          assert CallbackRunning(c, v, id.addr, id.cb);
          var tile', buf' :| CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile', buf') by {
            reveal CallbackRunning;
          }
          assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile', buf');
          assert CallbackPresentInBufferLocation(c, v, id.addr, id.cb, tile', buf');
          assert false;
        } else {
          assert id.count == v.g.callback_epochs[id.addr].epoch;
          assert id.addr.Morph?;
          assert !SpecCallbackId(c, v, id) by {
            if SpecCallbackId(c, v, id) {
              if id.cb.OnMiss? {
                assert CBOrderTrackerIndexIsRequest(c, v, id.addr, 0, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type);
                forall val
                  ensures !OnEvictInProgress(c, v, id.addr, val)
                  ensures !OnWritebackInProgress(c, v, id.addr, val)
                {}
                assert UnstartedCallbackPresent(c, v, id.addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type) by {
                  reveal UnstartedCallbackPresent;
                }
                assert CallbackPresent(c, v, id.addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type) by {
                  reveal CallbackPresent;
                }
                var c_idx := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type.idx;
                assert OnMissInProgress(c, v, id.addr, c_idx);
                if PrivateMorph(id.addr) {
                  reveal L2PendingCallbackForAddr;
                  assert v.tiles[id.addr.morphType.idx].l2.cache[c_idx].PendingCB?;
                } else {
                  assert SharedMorph(id.addr);
                  reveal L3PendingCallbackForAddr;
                  assert v.tiles[c.addr_map(id.addr)].l3.cache[c_idx].PendingCB?;
                }
                assert v.g.callback_epochs[id.addr].Out?;
              } else if id.cb.OnEvict? {
                assert UnstartedCallbackPresent(c, v, id.addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type) by {
                  reveal UnstartedCallbackPresent;
                }
                assert UnstartedOnEvictEntryForAddr(c, v, id.addr) by {
                  reveal UnstartedOnEvictEntryForAddr;
                }
                assert v.g.callback_epochs[id.addr].In?;
              } else {
                assert id.cb.OnWriteBack?;
                assert UnstartedCallbackPresent(c, v, id.addr, v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type) by {
                  reveal UnstartedCallbackPresent;
                }
                assert UnstartedOnWritebackEntryForAddr(c, v, id.addr) by {
                  reveal UnstartedOnWritebackEntryForAddr;
                }
                assert v.g.callback_epochs[id.addr].In?;
              }
            }
          }
        } 
      }
    }
  }

  lemma PerformNextInstPreservesAllWritesToAddrLessThanCurrentPCEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires UniqueTileForCallbackAddr(c, v)
    requires UniqueCurrentCallbacktoAddr(c, v)
    requires RunningCallbackValuesAgree(c, v)
    requires AllWritesToAddrLessThanCurrentPCEngine(c, v)
    ensures AllWritesToAddrLessThanCurrentPCEngine(c, v')
  {
    forall addr: Address, idx: nat, id: ThreadId, tile: nat, buf: nat | (
      && addr in v'.g.writes_to_addr
      && idx < |v'.g.writes_to_addr[addr]|
      && CurrentSpecCallbackId(c, v', id)
      && CallbackRunningInBufferLocation(c, v', id.addr, id.cb, tile, buf)
      && v'.g.writes_to_addr[addr][idx].info.id == id
    ) 
    ensures (
      && v'.g.writes_to_addr[addr][idx].info.pc.less_than(
        PC(v'.tiles[tile].engine.buffer[buf].pc, v'.tiles[tile].engine.buffer[buf].count)
      )
    )
    {
      if step.tile_step.EngineStep?
        && v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr == id.addr
        && EngReqToCBType(v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type) == id.cb
      {
        assert CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile, buf);
        assert CurrentSpecCallbackId(c, v, id);
        if (
          || step.tile_step.eng_step.inst.RMW? 
          || step.tile_step.eng_step.inst.Store?
          || step.tile_step.eng_step.inst.Load? 
          || step.tile_step.eng_step.inst.Branch?
        ) {
          assert CallbackPresentInBufferLocation(c, v, id.addr, id.cb, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, id.addr, id.cb, step.tile_idx, step.tile_step.eng_step.idx);
        } 
      }
    }
  }

  lemma NoOpPreservesWritesToAddrHaveValidThreadIds(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires WritesToAddrHaveValidThreadIds(c, v)
    ensures WritesToAddrHaveValidThreadIds(c, v')
  {}

  lemma StartEndCBPreservesWritesToAddrHaveValidThreadIds(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires WritesToAddrHaveValidThreadIds(c, v)
    ensures WritesToAddrHaveValidThreadIds(c, v')
  {}
  
  lemma PerformNextInstPreservesWritesToAddrHaveValidThreadIds(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires WritesToAddrHaveValidThreadIds(c, v)
    ensures WritesToAddrHaveValidThreadIds(c, v')
  {}
}