open util/relation
////////////////////////////////////////////////////////////////////////////////
// Utility



// squaring
fun sq[x: set Event] : Event->Event {
  x->x
}

fun optional[f: univ->univ] : univ->univ {
  f + iden
}


// irreflexive total order
pred strictTotalOrder[x: univ->univ, y: univ] {
  irreflexive[x]
  transitive[x]
  complete[x, y]
}

////////////////////////////////////////////////////////////////////////////////
// =Basic model of memory=


abstract sig Address {
  addrType: one AddrType,
  accessType: one AccessType // Synch or Data
}

// don't use ints as it complicates modelling
enum Val { Zero, One, Two, Three }

enum DirtyBit { Clean, Dirty }

enum AccessType { Synch, Data }

enum AddrType {
  Regular,
  SharedMorph,
  PrivateMorph
}

abstract sig Event { 
  address: one Address,
  thd: set Event, //thd equivalence relation
  sb: set Event,  // sequenced before
}

// R, W, RMW on standard mem
abstract sig MemoryEvent extends Event {}

// RegRead in Dafny
sig ReadEvent in MemoryEvent {
  rval: one Val,
}

// RegWrite in Dafny
sig WriteEvent in MemoryEvent { 
  wval: one Val,
  rf: set ReadEvent, 
  mo: set WriteEvent,
}

sig Read in MemoryEvent {}
sig Write in MemoryEvent {}
sig RMW in MemoryEvent {}

fact {
  MemoryEvent = ReadEvent + WriteEvent
  Read = MemoryEvent - WriteEvent
  Write = MemoryEvent - ReadEvent
  RMW = ReadEvent & WriteEvent
}

abstract sig CallbackEvent extends Event {
  cbo: set CallbackEvent, // callback order (extended with Rcb and Wcb events)
}

sig Flush extends CallbackEvent {}
abstract sig CallbackMemEvent extends CallbackEvent {}
abstract sig CallbackTimeEvent extends CallbackEvent {}

// callback memory accesses
sig ReadCBEvent in CallbackMemEvent {
  rval: one Val,
}
sig WriteCBEvent in CallbackMemEvent {
  wval: one Val,
}

sig ReadCB in CallbackMemEvent {}
sig WriteCB in CallbackMemEvent {}
sig RMWCB in CallbackMemEvent {}

fact {
  CallbackMemEvent = ReadCBEvent + WriteCBEvent
  ReadCB = CallbackMemEvent - WriteCBEvent
  WriteCB = CallbackMemEvent - ReadCBEvent
  RMWCB = ReadCBEvent & WriteCBEvent
}

// callback time events
sig MissStart extends CallbackTimeEvent {}
sig MissEnd extends CallbackTimeEvent {
  val: one Val, // end of OnMiss produces value
}

sig EvictStart extends CallbackTimeEvent { // start of OnEvict/WB
  val: one Val, // value to write back
  dirty: one DirtyBit, 
}

sig EvictEnd extends CallbackTimeEvent {
  dirty: one DirtyBit,
}

sig InitialEvent in Event {}


////////////////////////////////////////////////////////////////////////////////
// Derived Relations
fun vf: Event->Event {
  (MissEnd->CallbackMemEvent) & (cbo - cbo.(CallbackTimeEvent <: iden).cbo)
}

fun ef : Event->Event {
  (MissEnd->EvictStart) & (cbo - cbo.(CallbackTimeEvent <: iden).cbo)
}

fun fv: Event->Event {
  ~vf.ef
}

fun fr: Event->Event {
  ~rf.mo
}

fun eco: Event->Event {
  ^(rf + mo + fr)
}

fun viscb: Event->Event {
  // WCB/Me -> RCB/Es that is in cbo but not in a chain interrupted by another Wcb or time event 
  (WriteCBEvent + MissEnd)->(ReadCBEvent + EvictStart) & (cbo - (cbo.((WriteCBEvent + CallbackTimeEvent) <: iden).cbo))
}

fun sw: Event->Event {
  (RMW + RMWCB) <: (cbo + rf) :> (RMW + RMWCB)
}

fun eb: Event->Event {
  (EvictEnd->Flush) & (cbo - (cbo.(CallbackTimeEvent <: iden).cbo))
}


fun hb: Event->Event {
  ^(
    sb + 
    (InitialEvent->(Event - InitialEvent)) +
    vf +
    ((MissEnd->EvictStart) & cbo) +
    ((EvictEnd->MissStart) & cbo) +
    eb +
    sw
  )
}

fun vis: Event->Event {
  Write->Read & (hb - (hb.(Write <: iden).hb))
}

fun race: Event->Event {
  // no RMWs for race
  ((
    Read->Write +
    Write->Read +
    Write->Write +
    ReadCB->WriteCB +
    WriteCB->ReadCB +
    WriteCB->WriteCB
  ) & address.iden.~address)
  - iden
  - hb
  - ~hb
}

////////////////////////////////////////////////////////////////////////////////
// Well-formed Axioms

// thread ignores initial events and is an equivalence relation
fact {
  all i : InitialEvent | i in Write and (Write <: i).wval = Zero
  thd in sq[Event - InitialEvent]
  equivalence[thd, Event - InitialEvent]
}

// sequenced before is a strict partial order subset of thd
fact {
  sb in thd
  irreflexive[sb]
  transitive[sb]
  all e: Event | complete[sb, e.thd]
}

fact WfRf {
  // every read has a write sequenced before it
  all r : ReadEvent | one w : WriteEvent | w->r in rf
  // locations and values match for rf
  all r: ReadEvent, w: WriteEvent | w->r in rf implies r.address = w.address
  all r: ReadEvent, w: WriteEvent | w->r in rf implies r.rval = w.wval
}

fact WfMo {
  // mo is a strict total order on each address
  all a: Address | strictTotalOrder[mo, a.~address :> WriteEvent]
  // locations match
  all w1, w2: WriteEvent | w1 in w2.mo implies w1.address = w2.address
}

fact WfCbo {
  // cbo is a strict total order on each address
  all a: Address | strictTotalOrder[cbo, a.~address :> CallbackEvent]
  // locations match
  all c1, c2: CallbackEvent | c1 in c2.cbo implies c1.address = c2.address

  // start and end of same thread in cbo
  ((MissStart->MissEnd) & thd) in cbo
  ((EvictStart->EvictEnd) & thd) in cbo

  // no intervening
  no (MissStart <: cbo.cbo :> MissEnd) & thd
  no (EvictStart <: cbo.cbo :> EvictEnd) & thd

  // Me -> Ms must have Me -> Es -> Ee -> Ms
  MissEnd <: cbo :> MissStart in MissEnd <: cbo.((EvictStart->EvictEnd) & thd).cbo :> MissStart

  // Ee -> Es must have Ee -> Ms -> Me -> Es
  EvictEnd <: cbo :> EvictStart in EvictEnd <: cbo.((MissStart->MissEnd) & thd).cbo :> EvictStart

  // Ms -> Ms must have Ms -> Me -> Ms
  MissStart <: cbo :> MissStart in MissStart <: ((MissStart->MissEnd) & thd).cbo :> MissStart

  // Es -> Es must have Es -> Ee -> Es
  EvictStart <: cbo :> EvictStart in EvictStart <: ((EvictStart->EvictEnd) & thd).cbo :> EvictStart
  
  // start and end pair in callback threads
  all me: MissEnd | one ms: MissStart | me in ms.thd // and ms.address = me.address

  all ee: EvictEnd | one es: EvictStart | ee in es.thd //  and es.address = ee.address

  // every callback read/write has a Me sequenced before it
  all rwcb: CallbackMemEvent | one m: MissEnd | rwcb in m.vf

  // every eviction has a Me sequenced before it
  all es: EvictStart | one m: MissEnd | es in m.ef

  // every flush is either pre all missstarts or has a unique EvictEnd before it
  all f: Flush | 
    (all ms: MissStart | ms.address = f.address implies f->ms in cbo) or 
    (one ee: EvictEnd | f in ee.eb)

  // every callback read gets either the value from the miss end or the write that most recently preceded it
  all rcb: ReadCBEvent, wcb: WriteCBEvent | wcb->rcb in viscb implies wcb.wval = rcb.rval
  all rcb: ReadCBEvent, me: MissEnd | me->rcb in viscb implies me.val = rcb.rval

  // every evict start gets either the value from the miss end or the write that most recently preceded it
  all es: EvictStart, wcb: WriteCBEvent | wcb->es in viscb implies wcb.wval = es.val
  all es: EvictStart, me: MissEnd | me->es in viscb implies me.val = es.val

  // if an Es is dirty, the most recent visible access to address must be a write/rmw
  all es: EvictStart | es.dirty = Dirty implies some wcb : WriteCBEvent | wcb->es in viscb

  // conversely, if clean, there is no write/rmw
  all es: EvictStart | es.dirty = Clean implies no wcb : WriteCBEvent | wcb->es in viscb

  // bookkeeping, evict starts and ends must match dirty bit
  all es: EvictStart, ee: EvictEnd | es->ee in thd implies es.dirty = ee.dirty
}


// only references the preexec -- properties of a well-formed program
fact WfAddr {
  all cbe: CallbackEvent | cbe.address.addrType = SharedMorph or cbe.address.addrType = PrivateMorph
  all r: MemoryEvent | r.address.addrType = Regular
  all rmw: RMW | rmw.address.accessType = Synch
  all rmw: RMWCB | rmw.address.accessType = Synch
  all r: Read | r.address.accessType = Data
  all w: Write | (w not in InitialEvent) implies w.address.accessType = Data
  all r: ReadCB | r.address.accessType = Data
  all w: WriteCB | w.address.accessType = Data
}

fact WfPreExec {

  // only read shared morph data from private callback
  all ms: MissStart | all rwcb: CallbackMemEvent | (rwcb in ms.thd and ms.address.addrType = PrivateMorph) implies rwcb.address.addrType = SharedMorph
  all ms: MissStart | ms.address.addrType = SharedMorph implies (no rwcb: CallbackMemEvent | rwcb in ms.thd)


  // only access shared morph data from private callback
  all es: EvictStart | all rwcb: CallbackMemEvent | (rwcb in es.thd and es.address.addrType = PrivateMorph) implies rwcb.address.addrType = SharedMorph
  all es: EvictStart | es.address.addrType = SharedMorph implies (no rwcb: CallbackMemEvent | rwcb in es.thd)


  // Private Morph can only be accessed by one thread
  all e1, e2: Event | e1.address = e2.address and e1.address.addrType = PrivateMorph implies e1.thd = e2.thd


  // can't do callback read from same addr in callback
  all rwcb: CallbackMemEvent, ms: MissStart | rwcb in ms.thd implies rwcb.address != ms.address
  all rwcb: CallbackMemEvent, es: EvictStart | rwcb in es.thd implies rwcb.address != es.address
}




////////////////////////////////////////////////////////////////////////////////
// Consistency Axioms 


fact HB {
  irreflexive[hb]
}

fact Coh {
  irreflexive[eco.hb]
}

fact CbCoh {
  irreflexive[cbo.hb]
}

fact RMW {
  irreflexive[rf + mo.mo.~rf + mo.rf]
}