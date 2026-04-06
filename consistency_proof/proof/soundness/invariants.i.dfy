include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"

module SpecConsistencyInvariants {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec

  // Helper Predicates
  // {

  ghost predicate IncompleteThread(c: Constants, v: Variables, t: ThreadId)
  {
    && t in v.pcs
    && !v.pcs[t].pc.End?
  }

  ghost predicate CallbackThread(c: Constants, v: Variables, t: ThreadId)
  {
    && t in v.pcs
    && t.CallbackId?
  }

  ghost predicate OnMissThread(c: Constants, v: Variables, t: ThreadId)
  {
    && CallbackThread(c, v, t)
    && t.cb.OnMiss?
  }

  ghost predicate OnEvictThread(c: Constants, v: Variables, t: ThreadId)
  {
    && CallbackThread(c, v, t)
    && t.cb.OnEvict?
  }

  ghost predicate OnWBThread(c: Constants, v: Variables, t: ThreadId)
  {
    && CallbackThread(c, v, t)
    && t.cb.OnWriteBack?
  }

  ghost predicate IncompleteOnMiss(c: Constants, v: Variables, t: ThreadId)
  {
    && IncompleteThread(c, v, t)
    && OnMissThread(c, v, t)
  }

  ghost predicate IncompleteOnEvict(c: Constants, v: Variables, t: ThreadId)
  {
    && IncompleteThread(c, v, t)
    && OnEvictThread(c, v, t)
  }

  ghost predicate IncompleteOnWB(c: Constants, v: Variables, t: ThreadId)
  {
    && IncompleteThread(c, v, t)
    && OnWBThread(c, v, t)
  }




  ghost predicate AddrOutEpoch(c: Constants, v: Variables, addr: Address)
  {
    && addr in v.epochs
    && v.epochs[addr].Out?
  }

  ghost predicate AddrMissEpoch(c: Constants, v: Variables, addr: Address)
  {
    && addr in v.epochs
    && v.epochs[addr].Miss?
  }

  ghost predicate AddrInEpoch(c: Constants, v: Variables, addr: Address)
  {
    && addr in v.epochs
    && v.epochs[addr].In?
  }

  ghost predicate AddrEvictEpoch(c: Constants, v: Variables, addr: Address)
  {
    && addr in v.epochs
    && v.epochs[addr].Evict?
  }


  ghost predicate WFEvent(c: Constants, v: Variables, e: Event)
  {
    && e.WF()
    && e in v.execution.pre.events
  }

  ghost predicate WFMissStart(c: Constants, v: Variables, e: Event)
  {
    && e.WF()
    && e in v.execution.MissStarts()
  }

  ghost predicate WFEvictStart(c: Constants, v: Variables, e: Event)
  {
    && e.WF()
    && e in v.execution.EvictStarts()
  }

  ghost predicate WFMissEnd(c: Constants, v: Variables, e: Event)
  {
    && e.WF()
    && e in v.execution.MissEnds()
  }

  ghost predicate WFEvictEnd(c: Constants, v: Variables, e: Event)
  {
    && e.WF()
    && e in v.execution.EvictEnds()
  }

  ghost predicate WFCallBackBookends(c: Constants, v: Variables, e: Event)
  {
    && e.WF()
    && (
      || e in v.execution.MissStarts()
      || e in v.execution.EvictStarts()
      || e in v.execution.MissEnds()
      || e in v.execution.EvictEnds()
    )
  }


  ghost predicate WFWcb(c: Constants, v: Variables, e: Event)
  {
    && e.WF()
    && (e.Wcb? || e.RMWcb?)
    && e in v.execution.pre.events
  }

  ghost predicate WFW(c: Constants, v: Variables, e: Event)
  {
    && e.WF()
    && e.W?
    && e in v.execution.pre.events
  }

  ghost predicate WFR(c: Constants, v: Variables, e: Event)
  {
    && e.WF()
    && e.R?
    && e in v.execution.pre.events
  }

  // }


  // Invariants

  ghost predicate InfoInPCTrackerMeansEventInExecution(c: Constants, v: Variables)
  {
    (forall e: Event | (
      e in v.execution.pre.events
    ) ::
      (
        || e.info.id in v.pcs
        || e.info.id.Initial?
      )
    )
  }

  ghost predicate PCTrackerEnsuresUniqueEvents(c: Constants, v: Variables)
  {
    (forall id : ThreadId, e : Event | (
      && IncompleteThread(c, v, id)
      && e in v.execution.pre.events
      && e.info.id == id
    ) ::
      e.info.pc.less_than(v.pcs[id].pc)
    )
  }

  ghost predicate InitialWriteExistsForallAddr(c: Constants, v: Variables)
  {
    // all addresses have an initial write
    && (forall addr: Address | addr in c.p.WorkingSet() && addr.Regular? ::
      W(addr, Just(0), ThreadInfo(Initial(), Start())) in v.execution.pre.events
    )
  }

  ghost predicate AllEventsWellFormed(c: Constants, v: Variables)
  {
    // all starts have pc start
    && (forall e: Event | e in v.execution.pre.events ::
      e.WF()
    )
  }


  ghost predicate IncompleteOnMissMeansMissEpoch(c: Constants, v: Variables)
  {
    forall t: ThreadId | IncompleteOnMiss(c, v, t) :: (
      && AddrMissEpoch(c, v, t.addr)
      && v.epochs[t.addr].epoch == t.count
    )
  }

  ghost predicate IncompleteOnEvictMeansEvictEpoch(c: Constants, v: Variables)
  {
    forall t: ThreadId | IncompleteOnEvict(c, v, t) || IncompleteOnWB(c, v, t) :: (
      && AddrEvictEpoch(c, v, t.addr)
      && v.epochs[t.addr].epoch == t.count
      && v.epochs[t.addr].dirty == (t.cb.OnWriteBack?)
      && EvictReg() in v.pcs[t].regs
      && v.epochs[t.addr].val == v.pcs[t].regs[EvictReg()]
    )
  }

  ghost predicate MissEpochExistingEvents(c: Constants, v: Variables)
  {
    && (forall addr: Address | AddrMissEpoch(c, v, addr) :: (
      && var ms := Ms(addr, ThreadInfo(CallbackId(addr, OnMiss(), v.epochs[addr].epoch), Start()));
      && ms in v.execution.pre.events
      && (forall e : Event | e in v.execution.pre.events :: !((ms, e) in v.execution.wit.cbo))
    ))
  }


  ghost predicate EvictEpochExistingEvents(c: Constants, v: Variables)
  {
    && (forall addr: Address | AddrEvictEpoch(c, v, addr) :: (
      && var cb := if v.epochs[addr].dirty then OnWriteBack() else OnEvict();
      && var es := Es(addr, v.epochs[addr].val, v.epochs[addr].dirty, ThreadInfo(CallbackId(addr, cb, v.epochs[addr].epoch), Start()));
      && es in v.execution.pre.events
      && (forall val' | val' != v.epochs[addr].val
        :: !(Es(addr, val', v.epochs[addr].dirty, ThreadInfo(CallbackId(addr, cb, v.epochs[addr].epoch), Start())) in v.execution.pre.events))
      && (forall e : Event | e in v.execution.pre.events :: !((es, e) in v.execution.wit.cbo))
    ))
  }

  ghost predicate OneIncompletePerAddress(c: Constants, v: Variables)
  {
    && (forall t: ThreadId, t': ThreadId | IncompleteThread(c, v, t) && CallbackThread(c, v, t) && CallbackThread(c, v, t') && t != t' && t'.addr == t.addr :: (
        !IncompleteThread(c, v, t')
    ))
  }

  ghost predicate InOutEpochMeansNoIncomplete(c: Constants, v: Variables)
  {
    && (forall t: ThreadId | IncompleteThread(c, v, t) && CallbackThread(c, v, t) :: (
      && !AddrInEpoch(c, v, t.addr)
      && !AddrOutEpoch(c, v, t.addr)
    ))
  }

  // cbowf3

  ghost predicate BookEndsOutEpoch(c: Constants, v: Variables) {
    forall e: Event | WFCallBackBookends(c, v, e) && AddrOutEpoch(c, v, e.addr) ::
      e.info.id.count < v.epochs[e.addr].epoch
  }

  ghost predicate BookEndsMissEpoch(c: Constants, v: Variables) {
    forall e: Event | WFCallBackBookends(c, v, e) && AddrMissEpoch(c, v, e.addr) ::
      && (!WFMissStart(c, v, e) ==> e.info.id.count < v.epochs[e.addr].epoch)
      && (WFMissStart(c, v, e) ==> e.info.id.count <= v.epochs[e.addr].epoch)
  }

  ghost predicate BookEndsInEpoch(c: Constants, v: Variables) {
    forall e: Event | WFCallBackBookends(c, v, e) && AddrInEpoch(c, v, e.addr) ::
      && (!(WFMissStart(c, v, e) || WFMissEnd(c, v, e)) ==> e.info.id.count < v.epochs[e.addr].epoch)
      && ((WFMissStart(c, v, e) || WFMissEnd(c, v, e)) ==> e.info.id.count <= v.epochs[e.addr].epoch)
  }

  ghost predicate BookEndsEvictEpoch(c: Constants, v: Variables) {
    forall e: Event | WFCallBackBookends(c, v, e) && AddrEvictEpoch(c, v, e.addr) ::
      && (WFEvictEnd(c, v, e) ==> e.info.id.count < v.epochs[e.addr].epoch)
      && (!WFEvictEnd(c, v, e) ==> e.info.id.count <= v.epochs[e.addr].epoch)
  }


  ghost predicate LowerEpochImpliesCbo(c: Constants, v: Variables) {
    forall e1: Event, e2: Event | WFCallBackBookends(c, v, e1) && WFCallBackBookends(c, v, e2) && e1.info.id.count < e2.info.id.count && SameAddr(e1.addr, e2.addr) ::
      (
        && (e1, e2) in v.execution.wit.cbo
        && !((e2, e1) in v.execution.wit.cbo)
      )
  }

  ghost predicate SameEpochImpliesCbo(c: Constants, v: Variables) {
    forall e1: Event, e2: Event | WFCallBackBookends(c, v, e1) && WFCallBackBookends(c, v, e2) && e1.info.id.count == e2.info.id.count && SameAddr(e1.addr, e2.addr) :: (
      ((e1, e2) in v.execution.wit.cbo)
      <==>
      (
        || (WFMissStart(c, v, e1) && (
          || WFMissEnd(c, v, e2)
          || WFEvictStart(c, v, e2)
          || WFEvictEnd(c, v, e2)
          )
        )
        || (WFMissEnd(c, v, e1) && (
          || WFEvictStart(c, v, e2)
          || WFEvictEnd(c, v, e2)
          )
        )
        || (WFEvictStart(c, v, e1) && WFEvictEnd(c, v, e2))
      )
    )
  }

  ghost predicate LowerEpochExistingEventsN(c: Constants, v: Variables)
  {
    && (forall addr: Address, n: nat | addr in v.epochs && n < v.epochs[addr].epoch :: (
      && var ms := Ms(addr, ThreadInfo(CallbackId(addr, OnMiss(), n), Start()));
      && (ms in v.execution.pre.events)
      && var t := CallbackId(addr, OnMiss(), n);
      && t in v.pcs
      && var val := Transform(v.pcs[CallbackId(addr, OnMiss(), n)].vals);
      && var me := Me(addr, val, ThreadInfo(CallbackId(addr, OnMiss(), n), End()));
      && (me in v.execution.pre.events)
      && var clean_e := Ee(addr, false, ThreadInfo(CallbackId(addr, OnEvict(), n), End()));
      && var dirty_e := Ee(addr, true, ThreadInfo(CallbackId(addr, OnWriteBack(), n), End()));
      && var clean_s_exists := (exists val: Value :: Es(addr, val, false, ThreadInfo(CallbackId(addr, OnEvict(), n), Start())) in v.execution.pre.events);
      && var dirty_s_exists := (exists val: Value :: Es(addr, val, true, ThreadInfo(CallbackId(addr, OnWriteBack(), n), Start())) in v.execution.pre.events);
      && (clean_s_exists != dirty_s_exists)
      && (clean_s_exists <==> clean_e in v.execution.pre.events)
      && (dirty_s_exists <==> dirty_e in v.execution.pre.events)
    ))
  }

  ghost predicate EvictEpochExistingEventsN(c: Constants, v: Variables)
  {
    && (forall addr: Address | AddrEvictEpoch(c, v, addr) :: (
      && var ms := Ms(addr, ThreadInfo(CallbackId(addr, OnMiss(), v.epochs[addr].epoch), Start()));
      && ms in v.execution.pre.events
      && var t := CallbackId(addr, OnMiss(), v.epochs[addr].epoch);
      && t in v.pcs
      && var val := Transform(v.pcs[CallbackId(addr, OnMiss(), v.epochs[addr].epoch)].vals);
      && var me := Me(addr, val, ThreadInfo(CallbackId(addr, OnMiss(), v.epochs[addr].epoch), End()));
      && (me in v.execution.pre.events)
      && var cb := if v.epochs[addr].dirty then OnWriteBack() else OnEvict();
      && var es := Es(addr, v.epochs[addr].val, v.epochs[addr].dirty, ThreadInfo(CallbackId(addr, cb, v.epochs[addr].epoch), Start()));
      && es in v.execution.pre.events
      && (v.epochs[addr].dirty ==> 
        (forall val: Value :: !(Es(addr, val, false, ThreadInfo(CallbackId(addr, OnEvict(), v.epochs[addr].epoch), Start())) in v.execution.pre.events))
      )
      && (!v.epochs[addr].dirty ==> 
        (forall val: Value :: !(Es(addr, val, true, ThreadInfo(CallbackId(addr, OnWriteBack(), v.epochs[addr].epoch), Start())) in v.execution.pre.events))
      )
    ))
  }

  ghost predicate InEpochExistingEventsN(c: Constants, v: Variables)
  {
    && (forall addr: Address | AddrInEpoch(c, v, addr) :: (
      && var ms := Ms(addr, ThreadInfo(CallbackId(addr, OnMiss(), v.epochs[addr].epoch), Start()));
      && ms in v.execution.pre.events
      && var t := CallbackId(addr, OnMiss(), v.epochs[addr].epoch);
      && t in v.pcs
      && var val := Transform(v.pcs[CallbackId(addr, OnMiss(), v.epochs[addr].epoch)].vals);
      && var me := Me(addr, val, ThreadInfo(CallbackId(addr, OnMiss(), v.epochs[addr].epoch), End()));
      && (me in v.execution.pre.events)
    ))
  }

  ghost predicate MissEpochExistingEventsN(c: Constants, v: Variables)
  {
    && (forall addr: Address | AddrMissEpoch(c, v, addr) :: (
      && var ms := Ms(addr, ThreadInfo(CallbackId(addr, OnMiss(), v.epochs[addr].epoch), Start()));
      && ms in v.execution.pre.events
    ))
  }


  // cbowf4
  ghost predicate InEpochMeIsMissEnd(c: Constants, v: Variables)
  {
    forall addr: Address | AddrInEpoch(c, v, addr) :: (
      && WFMissEnd(c, v, v.epochs[addr].me)
      && v.epochs[addr].epoch == v.epochs[addr].me.info.id.count
      && v.epochs[addr].me.addr == addr
    )
  }

  ghost predicate MeEventsUniquePerEpoch(c: Constants, v: Variables)
  {
    // all starts have pc start
    && (forall e1: Event, e2: Event | WFMissEnd(c, v, e1) && WFMissEnd(c, v, e2) ::
      e1.info.id == e2.info.id ==> e1 == e2
    )
  }

  ghost predicate IrreflexiveCbo(c: Constants, v: Variables)
  {
    // all starts have pc start
    && (forall e: Event | e in v.execution.pre.events ::
      !((e, e) in v.execution.wit.cbo)
    )
    && (forall e1: Event, e2: Event | (e1, e2) in v.execution.wit.cbo ::
      SameAddr(e1.addr, e2.addr)
    )
  }

  //cbowf5

  ghost predicate InEpochWcbIsWriteCBorRMWCB(c: Constants, v: Variables)
  {
    forall addr: Address | AddrInEpoch(c, v, addr) && v.epochs[addr].wcb.Some? :: (
      && var wcb := v.epochs[addr].wcb.val;
      && wcb.WF()
      && (wcb.Wcb? || wcb.RMWcb?)
      && wcb.addr == addr
      && (forall e : Event | (WFCallBackBookends(c, v, e) || WFWcb(c, v, e)) && e.addr == addr :: (
        && !((wcb, e) in v.execution.wit.cbo)
        && ((e != wcb) ==> (e, wcb) in v.execution.wit.cbo)
      ))
    )
  }

  ghost predicate InEpochNoWcbMeansMeIsLast(c: Constants, v: Variables)
  {
    forall addr: Address | AddrInEpoch(c, v, addr) && v.epochs[addr].wcb.None? :: (
      && (forall e : Event | (WFCallBackBookends(c, v, e) || WFWcb(c, v, e)) && e.addr == addr :: (
        && !((v.epochs[addr].me, e) in v.execution.wit.cbo)
        && ((e != v.epochs[addr].me) ==> (e, v.epochs[addr].me) in v.execution.wit.cbo)
      ))
    )
  }


  /*


  ghost predicate MsEventsUniquePerEpoch(c: Constants, v: Variables)
  {
    // all starts have pc start
    && (forall e1: Event, e2: Event | WFMissStart(c, v, e1) && WFMissStart(c, v, e2) ::
      e1.info.id == e2.info.id ==> e1 == e2
    )
  }

  ghost predicate EsEventsUniquePerEpoch(c: Constants, v: Variables)
  {
    // all starts have pc start
    && (forall e1: Event, e2: Event | WFEvictStart(c, v, e1) && WFEvictStart(c, v, e2) ::
      (
        && e1.info.id.count == e2.info.id.count
        && e1.info.id.addr == e2.info.id.addr
      ) ==> e1 == e2
    )
  }


  ghost predicate HigherEpochExistingMissStarts(c: Constants, v: Variables)
  {
    && (forall e : Event | WFMissStart(c, v, e) && e.info.id.addr in v.epochs ::
      e.info.id.count <= v.epochs[e.info.id.addr].epoch
    )
  }


  ghost predicate MsEsSameEpochInCbo(c: Constants, v: Variables)
  {
    && (forall ms: Event, es: Event | WFMissStart(c, v, ms) && WFEvictStart(c, v, es) :: (
      (
        && ms.info.id.addr == ms.info.id.addr
        && es.info.id.count == es.info.id.count
      ) ==> (ms, es) in v.execution.wit.cbo
    ))
  }




  ghost predicate AllStartsHavePCStart(c: Constants, v: Variables)
  {
    // all starts have pc start
    && (forall e: Event | e in v.execution.MissStarts() ::
      e.info.pc == Start()
    )
    && (forall e: Event | e in v.execution.EvictStarts() ::
      e.info.pc == Start()
    )
  }
  */


}