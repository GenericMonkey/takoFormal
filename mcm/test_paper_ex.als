open tako

////////////////////////////////////////////////////////////////////////////////
// Litmus Test from Motivation Section
// 
// core 0     onMiss_X  onE_X onWB_X
// Wcb x 1    (2)       ()    W Y 1
// Rcb x
// R Y

// Allowed Outcome: Rcb X = 2, R Y = 1
// Forbidden Outcome: Rcb X = 2, R Y = 0

one sig X, Y extends Address {}

fact addr_info {
  X.addrType = SharedMorph
  Y.addrType = Regular
}

// y initialization
one sig InitY  in MemoryEvent {}

fact init {
  InitY in Write
  InitY.address = Y
  InitY.wval = Zero

  InitY in InitialEvent
  all e: Event | e in InitialEvent implies e = InitY
}

// main program instructions
one sig WcbX   in CallbackMemEvent {}
one sig RcbX   in CallbackMemEvent {}
one sig RY     in MemoryEvent {}


fact core0 {
  // address bindings
  WcbX in WriteCB
  WcbX.address = X
  WcbX.wval = One

  RcbX.address = X

  RY in Read
  RY.address = Y

  WcbX->RcbX in sb
  RcbX->RY in sb
  // only these events in this thread
  all e: Event | (WcbX->e in thd) implies e = WcbX or e = RcbX or e = RY
}


fact onmiss_x {
  // Ms -> Me
  all ms : MissStart |
    ms.address = X and
    (all e: Event | (ms->e in thd) implies e = ms or (
      e in MissEnd and (e <: MissEnd).val = Two
    ))
}

fact onevict_x {
  // Es -> Ee
  all es : EvictStart |
    es.dirty = Clean implies 
    (es.address = X and
    (all e: Event | (es->e in thd) implies e = es or (
      e in EvictEnd
    )))
}

fact onwb_x {
  // Es -> W Y 1 -> Ee
  all es : EvictStart | 
    es.dirty = Dirty implies 
    (es.address = X and
    (some w : Write | (
      w.address = Y and
      w.wval = One and
      (es->w in sb) and 
      (all e: Event | (es->e in thd) implies e = es or e = w or (
        e in EvictEnd and
        w->e in sb
      ))
    )))
}

// only allowable threads are core 0, onmiss x, onwb x, onevict x
fact allowed_threads {
  all e : Event |
    e in InitialEvent or
    WcbX->e in thd or
    (some ms: MissStart | ms->e in thd) or 
    (some es: EvictStart | es->e in thd)
}

run allowed {
  RcbX.rval = Two
  RY.rval = One
} for 11 Event

run forbidden {
  RcbX.rval = Two
  RY.rval = Zero
} for 11 Event