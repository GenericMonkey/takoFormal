include "types.s.dfy"
include "program.i.dfy"
include "relations_library.i.dfy"

module Execution {
  import opened Program
  import opened Types
  import opened EngineTypes
  import Library

  datatype CallbackType =
    | OnMiss()
    | OnEvict()
    | OnWriteBack()

  ghost function EngReqToCBType(req: EngineRequest) : (res: CallbackType)
  {
    match req {
      case OnMiss(_) => CallbackType.OnMiss()
      case OnEvict(_) => CallbackType.OnEvict()
      case OnWriteBack(_) => CallbackType.OnWriteBack()
    }
  }

  datatype ThreadId =
    | Initial()
    | CoreId(id: nat)
    | CallbackId(addr: Address, cb: CallbackType, count: nat)

  datatype PC =
    | Start()
    | PC(pc: nat, count: nat)
    | End()
  {
    ghost predicate less_than(other: PC)
    {
      match this {
        case Start() => !other.Start?
        case PC(pc, count) =>
          match other {
            case Start() => false
            case PC(pc2, count2) => count < count2 || (count == count2 && pc < pc2)
            case End() => true
          }
        case End() => false
      }
    }
  }

  datatype ThreadInfo = ThreadInfo(
    id: ThreadId,
    pc: PC
  )

  datatype Epoch =
    | Out(epoch: nat) // allows F and Ms
    | Miss(epoch: nat) // only allows Me
    | In(epoch: nat, me: Event, wcb: Option<Event>) // allows Rcb/Wcb and Es
    | Evict(epoch: nat, val: Value, dirty: bool) // only allows Ee

  datatype RuntimeData = RuntimeData(
    pc: PC,
    regs: map<Register, Value>,
    vals: seq<Value>
  )

  datatype Event =
    | R(addr: Address, val: Value, info: ThreadInfo)
    | Rcb(addr: Address, val: Value, info: ThreadInfo)
    | W(addr: Address, val: Value, info: ThreadInfo)
    | Wcb(addr: Address, val: Value, info: ThreadInfo)
    | RMW(addr: Address, rval: Value, wval: Value, info: ThreadInfo)
    | RMWcb(addr: Address, rval: Value, wval: Value, info: ThreadInfo)
    | F(addr: Address, info: ThreadInfo)
    | Ms(addr: Address, info: ThreadInfo)
    | Me(addr: Address, val: Value, info: ThreadInfo)
    | Es(addr: Address, val: Value, dirty: bool, info: ThreadInfo)
    | Ee(addr: Address, dirty: bool, info: ThreadInfo)
  {

    ghost predicate MemoryEvent() {
      || this.R?
      || this.W?
      || this.RMW?
    }

    ghost predicate RegRead() {
      || this.R?
      || this.RMW?
    }

    ghost predicate RegWrite() {
      || this.W?
      || this.RMW?
    }

    ghost predicate CBRead() {
      || this.Rcb?
      || this.RMWcb?
    }

    ghost predicate CBWrite() {
      || this.Wcb?
      || this.RMWcb?
    }

    ghost predicate CallbackEvent() {
      || this.F?
      || this.CallbackMemEvent()
      || this.CallbackTimeEvent()
    }

    ghost predicate CallbackMemEvent() {
      || this.Rcb?
      || this.Wcb?
      || this.RMWcb?
    }

    ghost predicate CallbackTimeEvent() {
      || this.Es?
      || this.Ee?
      || this.Ms?
      || this.Me?
    }

    ghost predicate WF() {
      && match this {
        case Ms(addr, info) => info.id.CallbackId? && info.id.cb.OnMiss? && info.id.addr == addr && info.pc.Start?
        case Me(addr, val, info) => info.id.CallbackId? && info.id.cb.OnMiss? && info.id.addr == addr && info.pc.End?
        case Es(addr, _, dirty, info) => (
          && info.id.CallbackId?
          && info.id.addr == addr
          && info.pc.Start?
          && (if dirty then info.id.cb.OnWriteBack? else info.id.cb.OnEvict?)
        )
        case Ee(addr, dirty, info) => (
          && info.id.CallbackId?
          && info.id.addr == addr
          && info.pc.End?
          && (if dirty then info.id.cb.OnWriteBack? else info.id.cb.OnEvict?)
        )
        case _ => true
      }
    }
  }



  datatype PreExecution = PreExecution(
    events: set<Event>
  ) {
    ghost predicate WF() {
      // proper subsets
      && true
    }

    ghost function thd() : (res: set<(Event, Event)>)
      ensures Library.equivalence(res)
    {
      set e1: Event, e2: Event |
        && e1 in this.events
        && e2 in this.events
        && e1.info.id == e2.info.id
      :: (e1, e2)
    }

    ghost function sb() : (res: set<(Event, Event)>)
      ensures Library.irreflexive(res)
      ensures Library.transitive(res)
      ensures Library.dom(res) <= this.events
      ensures Library.range(res) <= this.events
    {
      set e1e2 : (Event, Event) |
      e1e2 in this.thd()
      && e1e2.0.info.pc.less_than(e1e2.1.info.pc) :: e1e2
    }
  }

  datatype Witness = Witness(
    rf: set<(Event, Event)>,
    mo: set<(Event, Event)>,
    cbo: set<(Event, Event)>
  ) {
    ghost predicate WF(pre : PreExecution) {
      // rf is subset of events
      && (forall e1, e2 : Event | (e1, e2) in this.rf :: e1 in pre.events && e2 in pre.events && e1.RegWrite() && e2.RegRead())
      // mo is subset of events
      && (forall e1, e2 : Event | (e1, e2) in this.mo :: e1 in pre.events && e2 in pre.events && e1.RegWrite() && e2.RegWrite())
      // cbo is subset of events
      && (forall e1, e2 : Event | (e1, e2) in this.cbo :: e1 in pre.events && e2 in pre.events && e1.CallbackEvent() && e2.CallbackEvent())
    }

  }

  ghost predicate SameAddr(addr1: Address, addr2: Address) {
    addr1 == addr2
  }

  datatype Execution = Execution(
    pre: PreExecution,
    wit: Witness
  ) {
    ghost predicate WF() {
      && pre.WF()
      && wit.WF(pre)
    }
    // Event Sets
    ghost function Writes() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.RegWrite() :: e
    }

    ghost function Reads() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.RegRead() :: e
    }

    ghost function WriteCBs() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.CBWrite() :: e
    }

    ghost function ReadCBs() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.CBRead() :: e
    }

    ghost function Flushes() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.F? :: e
    }

    ghost function RMWs() : (res: set<Event>)
    {
      set e: Event | e in pre.events && (e.RMW? || e.RMWcb?) :: e
    }

    ghost function MissStarts() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.Ms? :: e
    }

    ghost function MissEnds() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.Me? :: e
    }

    ghost function EvictStarts() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.Es? :: e
    }

    ghost function EvictEnds() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.Ee? :: e
    }

    ghost function CallbackMemEvents() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.CallbackMemEvent() :: e
    }

    ghost function CallbackTimeEvents() : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.CallbackTimeEvent() :: e
    }

    // Derived Relations

    ghost function init_to_noninit() : (res: set<(Event, Event)>)
    {
      set e1, e2 : Event |
        && e1 in pre.events
        && e2 in pre.events
        && e1.info.id.Initial?
        && !e2.info.id.Initial?
      :: (e1, e2)
    }

    ghost function vf() : (res: set<(Event, Event)>)
    {
      Library.intersection(
        Library.prod(MissEnds(), CallbackMemEvents()),
        wit.cbo -
        Library.compose(
          wit.cbo,
          Library.compose(
            Library.iden(CallbackTimeEvents()),
            wit.cbo
          )
        )
      )
    }
    
    ghost function ef() : (res: set<(Event, Event)>)
    {
      Library.intersection(
        Library.prod(MissEnds(), EvictStarts()),
        wit.cbo -
        Library.compose(
          wit.cbo,
          Library.compose(
            Library.iden(CallbackTimeEvents()),
            wit.cbo
          )
        )
      )
    }

    ghost function me_es() : (res: set<(Event, Event)>)
    {
      Library.intersection(
        Library.prod(MissEnds(), EvictStarts()),
        wit.cbo
      )
    }

    ghost function ee_ms() : (res: set<(Event, Event)>)
    {
      Library.intersection(
        Library.prod(EvictEnds(), MissStarts()),
        wit.cbo
      )
    }

    ghost function eb() : (res: set<(Event, Event)>)
    {
      Library.intersection(
        Library.prod(EvictEnds(), Flushes()),
        wit.cbo -
        Library.compose(
          wit.cbo,
          Library.compose(
            Library.iden(CallbackTimeEvents()),
            wit.cbo
          )
        )
      )
    }

    ghost function sw() : (res: set<(Event, Event)>)
      ensures Library.dom(res) <= pre.events
      ensures Library.range(res) <= pre.events
    {
      Library.intersection(
        Library.prod(RMWs(), RMWs()),
        (wit.cbo + wit.rf)
      )
    }

    ghost opaque function hb_components() : (res: set<(Event, Event)>)
      ensures Library.dom(res) <= pre.events
      ensures Library.range(res) <= pre.events
    {
      pre.sb() +
      init_to_noninit() +
      vf() +
      me_es() +
      ee_ms() +
      eb() +
      sw()
    }

    ghost function hb() : (res: set<(Event, Event)>)
    {
      Library.trans_closure(hb_components())
    }

    ghost function fr() : (res: set<(Event, Event)>)
    {
      Library.compose(Library.inverse(wit.rf), wit.mo)
    }

    ghost function rfmofr() : (res: set<(Event, Event)>)
    {
      wit.rf + wit.mo + fr()
    }

    ghost opaque function rmwloops() : (res: set<(Event, Event)>)
    {
      wit.rf +
      Library.compose(
        wit.mo,
        Library.compose(
          wit.mo,
          Library.inverse(wit.rf)
        )
      ) +
      Library.compose(
        wit.mo,
        wit.rf
      )
    }

    ghost function eco() : (res: set<(Event, Event)>)
    {
      Library.trans_closure(rfmofr())
    }

    ghost function hbeco() : (res: set<(Event, Event)>)
    {
      Library.compose(hb(), eco())
    }

    ghost function hbcbo() : (res: set<(Event, Event)>)
    {
      Library.compose(hb(), wit.cbo)
    }

    ghost function viscb() : (res: set<(Event, Event)>)
    {
      Library.intersection(
        Library.prod(WriteCBs() + MissEnds(), ReadCBs() + EvictStarts()),
        wit.cbo -
        Library.compose(
          wit.cbo,
          Library.compose(
            Library.iden(WriteCBs() + CallbackTimeEvents()),
            wit.cbo
          )
        )
      )
    }

    ghost function vis() : (res: set<(Event, Event)>)
    {
      Library.intersection(
        Library.prod(Writes(), Reads()),
        hb() -
        Library.compose(
          hb(),
          Library.compose(
            Library.iden(Writes()),
            hb()
          )
        )
      )
    }

    /*
    ghost function invis() : (res: set<(Event, Event)>)
    {
      set e1, e2, e3 : Event |
        && e1 in events
        && e2 in events
        && e3 in events
        && (e1, e2) in hb()
        && e2.Write()
        && (e2, e3) in hb()
      :: (e1, e3)
    }
    */

    ghost predicate Consistent() {
      && WF()
      && RfWf()
      && MoWf()
      && CboWf()
      && Hb()
      && Coh()
      && CbCoh()
      // && Narf()
    }

    ghost predicate RfWf() {
      // for every read, there is a write (could be 0/init) precedes it to the same address with the same value
      && (forall r: Event | r in pre.events && r.RegRead() ::
        exists w: Event :: (
          && w in pre.events
          && w.RegWrite()
          && var rval := if r.R? then r.val else r.rval;
          && var wval := if w.W? then w.val else w.wval;
          && wval == rval
          && SameAddr(w.addr, r.addr)
          && (w, r) in wit.rf
        )
      )
      // unique write
      && (forall r, w1, w2 : Event | (
          && (w1, r) in wit.rf
          && (w2, r) in wit.rf
        ) :: (
          w1 == w2
        )
      )
      && (forall w, r : Event | (w, r) in wit.rf :: (
        && SameAddr(w.addr, r.addr) 
        && w.RegWrite()
        && r.RegRead()
        && var rval := if r.R? then r.val else r.rval;
        && var wval := if w.W? then w.val else w.wval;
        && wval == rval
      ))
    }

    ghost function WritesToAddr(addr: Address) : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.RegWrite() && SameAddr(e.addr, addr) :: e
    }

    ghost function CBEventsToAddr(addr: Address) : (res: set<Event>)
    {
      set e: Event | e in pre.events && e.CallbackEvent() && SameAddr(e.addr, addr) :: e
    }

    ghost predicate MoWf() {
      && MoWf1()
      && MoWf2()
    }

    ghost predicate MoWf1() {
      // total order on mo
      && (forall addr: Address :: Library.stricttotalorder(wit.mo, WritesToAddr(addr)))
    }

    ghost predicate MoWf2() {
      // if you are in mo, you are a write and to the same address
      && (forall w1, w2: Event | (w1, w2) in wit.mo :: /* w1.W? && w2.W? && */ SameAddr(w1.addr, w2.addr))
    }

    ghost predicate CboWf() {
      && CboWf1()
      && CboWf2()
      && CboWf3()
      && CboWf4()
      && CboWf5()
      && CboWf6()
      && CboWf7()
      && CboWf8()
      && CboWf9()
      && CboWf10()
    }

    ghost predicate CboWf1() {
      // total order on cbo
      && (forall addr: Address :: Library.stricttotalorder(wit.cbo, CBEventsToAddr(addr)))
      // if you are in cbo, you are a cacheevent and to the same address
      && (forall c1, c2: Event | (c1, c2) in wit.cbo :: SameAddr(c1.addr, c2.addr))
    }

    ghost predicate CboWf2() {
      // no intervening events between S and E of the same thread
      && CboWf2_1()
      && CboWf2_2()
    }

    ghost predicate CboWf2_1() {
      Library.intersection(
        pre.thd(),
        Library.compose(
          Library.iden(MissStarts()),
          Library.compose(
            wit.cbo,
            Library.compose(
              wit.cbo,
              Library.iden(MissEnds())
            )
          )
        )
      ) == {}
    }

    ghost predicate CboWf2_2() {
      Library.intersection(
        pre.thd(),
        Library.compose(
          Library.iden(EvictStarts()),
          Library.compose(
            wit.cbo,
            Library.compose(
              wit.cbo,
              Library.iden(EvictEnds())
            )
          )
        )
      ) == {}
    }

    ghost predicate CboWf3() {
      && CboWf3_1()
      && CboWf3_2()
      && CboWf3_3()
      && CboWf3_4()
    }

    ghost predicate CboWf3_1() {
      // Me -> Ms must have Me -> Es -> Ee -> Ms
      &&
      Library.compose(
        Library.iden(MissEnds()),
        Library.compose(
          wit.cbo,
          Library.iden(MissStarts())
        )
      ) <=
      Library.compose(
        Library.iden(MissEnds()),
        Library.compose(
          wit.cbo,
          Library.compose(
            Library.intersection(
              pre.thd(),
              Library.prod(
                (EvictStarts()),
                (EvictEnds())
              )
            ),
            Library.compose(
              wit.cbo,
              Library.iden(MissStarts())
            )
          )
        )
      )

    }

    // Ee -> Es must have Ee -> Ms -> Me -> Es
    ghost predicate CboWf3_2() {
      Library.compose(
        Library.iden(EvictEnds()),
        Library.compose(
          wit.cbo,
          Library.iden(EvictStarts())
        )
      ) <=
      Library.compose(
        Library.iden(EvictEnds()),
        Library.compose(
          wit.cbo,
          Library.compose(
            Library.intersection(
              pre.thd(),
              Library.prod(
                (MissStarts()),
                (MissEnds())
              )
            ),
            Library.compose(
              wit.cbo,
              Library.iden(EvictStarts())
            )
          )
        )
      )
    }
    
    // Ms -> Ms must have Ms -> Me -> Ms
    ghost predicate CboWf3_3() {
      &&
      Library.compose(
        Library.iden(MissStarts()),
        Library.compose(
          wit.cbo,
          Library.iden(MissStarts())
        )
      ) <=
      Library.compose(
        Library.iden(MissStarts()),
        Library.compose(
          Library.intersection(
            pre.thd(),
            Library.prod(
              (MissStarts()),
              (MissEnds())
            )
          ),
          Library.compose(
            wit.cbo,
            Library.iden(MissStarts())
          )
        )
      )
    }

    ghost predicate CboWf3_4() {
      // Es -> Es must have Es -> Ee -> Es
      &&
      Library.compose(
        Library.iden(EvictStarts()),
        Library.compose(
          wit.cbo,
          Library.iden(EvictStarts())
        )
      ) <=
      Library.compose(
        Library.iden(EvictStarts()),
        Library.compose(
          Library.intersection(
            pre.thd(),
            Library.prod(
              (EvictStarts()),
              (EvictEnds())
            )
          ),
          Library.compose(
            wit.cbo,
            Library.iden(EvictStarts())
          )
        )
      )
    }

    ghost predicate CboWf4() {
      // every callback read/write and eviction has a Me sequenced before it
      && CboWf4_1()
      && CboWf4_2()
    }

    // every callback read/write has a Me sequenced before it
    ghost predicate CboWf4_1() {
      && (forall e: Event | e in pre.events && e.CallbackMemEvent() ::
        (exists m : Event :: m.Me? && (m, e) in vf())
      )
      && (forall me1, me2, e | (me1, e) in vf() && (me2, e) in vf() :: me1 == me2)
    }

    // every Es has a Me sequenced before it
    ghost predicate CboWf4_2() {
      && (forall e: Event | e in pre.events && e.Es? ::
        (exists m : Event :: m.Me? && (m, e) in ef())
      )
      && (forall me1, me2, e | (me1, e) in ef() && (me2, e) in ef() :: me1 == me2)
    }

    ghost predicate CboWf5() {
      && CboWf5_1()
      && CboWf5_2()
    }

    // every callback read gets either the value from the miss end or the write that most recently preceded it
    ghost predicate CboWf5_1() {
      && (forall wcb: Event, rcb: Event | wcb.CBWrite() && rcb.CBRead() && (wcb, rcb) in viscb()
        :: (
          && var wval := if wcb.Wcb? then wcb.val else wcb.wval;
          && var rval := if rcb.Rcb? then rcb.val else rcb.rval;
          && wval == rval
        )
      )
      && (forall me: Event, rcb: Event | me.Me? && rcb.CBRead() && (me, rcb) in viscb()
        :: (
          && var rval := if rcb.Rcb? then rcb.val else rcb.rval;
          me.val == rval
        )
      )
    }

    // every callback read gets either the value from the miss end or the write that most recently preceded it
    ghost predicate CboWf5_2() {
      && (forall wcb: Event, es: Event | wcb.CBWrite() && es.Es? && (wcb, es) in viscb()
        :: (
          && var wval := if wcb.Wcb? then wcb.val else wcb.wval;
          && wval == es.val
        )
      )
      && (forall me: Event, es: Event | me.Me? && es.Es? && (me, es) in viscb()
        :: me.val == es.val
      )
    }

    // if an Es is dirty, the most recent visible access to address must be a write
    // conversely, if clean, there is no write
    ghost predicate CboWf6() {
      && (forall es: Event | es in pre.events && es.Es? && es.dirty ::
        (exists wcb : Event :: wcb.CBWrite() && (wcb, es) in viscb())
      )

      && (forall es: Event | es in pre.events && es.Es? && !es.dirty ::
        (forall wcb : Event | wcb in pre.events && wcb.CBWrite() :: !((wcb, es) in viscb()))
      )
    }

    // ((MissStart->MissEnd) & thd) in cbo
    // ((EvictStart->EvictEnd) & thd) in cbo
    ghost predicate CboWf7() {
      && Library.intersection(
        pre.thd(),
        Library.prod(
          MissStarts(),
          MissEnds()
        )
      ) <= wit.cbo

      && Library.intersection(
        pre.thd(),
        Library.prod(
          EvictStarts(),
          EvictEnds()
        )
      ) <= wit.cbo
    }

    // dirty bookkeeping
    ghost predicate CboWf8() {
      && (forall es: Event, ee: Event | es.Es? && ee.Ee? && (es, ee) in pre.thd() :: 
        es.dirty == ee.dirty
      )
    }

    // every flush is either pre all missstarts or has a unique EvictEnd before it
    // uniqueness of evict end
    ghost predicate CboWf9() {
      && (forall f: Event | f in pre.events && f.F? :: (
        || (forall ms: Event | ms in pre.events && ms.Ms? && SameAddr(ms.addr, f.addr) :: (f, ms) in wit.cbo)
        || (exists ee: Event :: ee in pre.events && ee.Ee? && (ee, f) in eb())
      ))
      && (forall f, ee1, ee2 | (ee1, f) in eb() && (ee2, f) in eb() :: (
        ee1 == ee2
      ))
    }

    ghost predicate CboWf10() {
      && CboWf10_1()
      && CboWf10_2()
    }

    // missstart and missend pair in callback threads
    // uniqueness of MissStart
    ghost predicate CboWf10_1() {
      && (forall me: Event | me in pre.events && me.Me? :: (
        (exists ms: Event :: ms in pre.events && ms.Ms? && (ms, me) in pre.thd())
      ))
      && (forall me, ms1: Event, ms2: Event | ms1.Ms? && ms2.Ms? && (ms1, me) in pre.thd() && (ms2, me) in pre.thd() :: (
        ms1 == ms2
      ))
    }

    // evictstart and evictend pair in callback threads
    // uniqueness of EvictEnd
    ghost predicate CboWf10_2() {
      && (forall ee: Event | ee in pre.events && ee.Ee? :: (
        (exists es: Event :: es in pre.events && es.Es? && (es, ee) in pre.thd())
      ))
      && (forall ee, es1: Event, es2: Event | es1.Es? && es2.Es? && (es1, ee) in pre.thd() && (es2, ee) in pre.thd() :: (
        es1 == es2
      ))
    }

    ghost predicate Hb() {
      Library.irreflexive(hb())
    }

    ghost predicate Coh() {
      Library.irreflexive(hbeco())
    }

    ghost predicate CbCoh() {
      Library.irreflexive(hbcbo())
    }

    ghost predicate RMW() {
      Library.irreflexive(rmwloops())
    }

    ghost predicate Init(p: Program)
    {
      && this == Execution(
        PreExecution(
          set addr: Address | addr in p.WorkingSet() && addr.Regular? :: W(addr, Just(0), ThreadInfo(Initial(), Start()))
        ),
        Witness({}, {}, {})
      )
    }
  }

/*
  ghost function Restriction(ex: Execution, e': set<Event>) : (res: Execution)
  {
    Execution(
      events := e',
      wit := Witness(
        sb := Library.restriction(ex.wit.sb, e'),
        rf := Library.restriction(ex.wit.rf, e'),
        mo := Library.restriction(ex.wit.mo, e'),
        cbo := Library.restriction(ex.wit.cbo, e'),
        vf := Library.restriction(ex.wit.vf, e')
      )
    )
  }

  lemma PrefixClosure(ex: Execution, e': set<Event>)
    requires ex.Consistent()
    requires e' <= ex.events
    // requires TODO: requires correct commit order
    ensures Restriction(ex, e').Consistent()
  {

  }
*/
}
