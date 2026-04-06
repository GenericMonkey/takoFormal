include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module CBOrderTrackerWFProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma NotEngineNoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires !step.tile_step.EngineStep?
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma EngineReceiveCallbackNoOpPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures FwdIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      if IsBufferEntry(c, v, t, b) {
        assert AddrInTileCBOrderTracker(c, v, addr, t);
      } else {
        assert AddrInTileCBOrderTracker(c, v', addr, t);
      }
    }
  }

  lemma EngineReceiveCallbackNoOpPreservesRevIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures RevIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {}

  lemma EngineReceiveCallbackNoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    EngineReceiveCallbackNoOpPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step);
    EngineReceiveCallbackNoOpPreservesRevIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step);
  }

  lemma EngineNotReceiveCallbackNoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    assert step.tile_step.eng_step.CacheCommunicationStep?;
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma MemoryNoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma NoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        if tile_step.EngineStep? {
          if tile_step.eng_step.ReceiveCallbackReqStep? {
            EngineReceiveCallbackNoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step);
          } else {
            EngineNotReceiveCallbackNoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step);
          }
        } else {
          NotEngineNoOpPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step);
        }
      }
    }
  }

  lemma StartOnEvictPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma StartOnMissPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnMiss
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma StartOnWritebackPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnWriteback
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma StartCBPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    if re == StartOnEvict {
      StartOnEvictPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    } else if re == StartOnMiss {
      StartOnMissPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    } else if re == StartOnWriteback {
      StartOnWritebackPreservesIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    } else {
      assert false; // This case should not happen
    }
  }

  lemma EndOnEvictPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures FwdIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma EndOnMissPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnMiss
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures FwdIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma EndOnWritebackPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnWriteback
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures FwdIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma EndCBPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures FwdIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    if re == EndOnEvict {
      EndOnEvictPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    } else if re == EndOnMiss {
      EndOnMissPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    } else if re == EndOnWriteback {
      EndOnWritebackPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    } else {
      assert false; // This case should not happen
    }
  }

  lemma EndCBPreservesRevIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures RevIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat
      | (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
      ensures
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
    {
      assert AddrInTileCBOrderTracker(c, v, addr, t);
      assert b in v.tiles[t].engine.cb_order[addr];
    }
  }

  lemma EndCBPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires NoDupIdxsInCBOrderTracker(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    EndCBPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    EndCBPreservesRevIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
  }

  lemma PerformNextInstPreservesRevIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures RevIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {}

  // Lots of resource
  lemma CorePerformNextInstPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.NextInstStep?
    requires FwdIdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures FwdIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma EnginePerformNextInstPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.NextInstStep?
    requires FwdIdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures FwdIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v', t, b)
        && v'.tiles[t].engine.buffer[b].addr == addr
      )
      ensures
      (
        && AddrInTileCBOrderTracker(c, v', addr, t)
        && b in v'.tiles[t].engine.cb_order[addr]
      )
    {
      assert IsBufferEntry(c, v, t, b);
      assert AddrInTileCBOrderTracker(c, v, addr, t);
    }
  }

  lemma PerformNextInstPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires FwdIdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures FwdIdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    if step.tile_step.CoreStep? {
      CorePerformNextInstPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    } else if step.tile_step.EngineStep? {
      EnginePerformNextInstPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    } else {
      assert false; // This case should not happen
    }
  }

  lemma PerformNextInstPreservesIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    ensures IdxInCBOrderTrackerIffCallbackPresent(c, v')
  {
    PerformNextInstPreservesFwdIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
    PerformNextInstPreservesRevIdxInCBOrderTrackerIffCallbackPresent(c, v, v', step, re);
  }
}