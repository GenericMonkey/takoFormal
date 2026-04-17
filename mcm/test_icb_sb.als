open tako

////////////////////////////////////////////////////////////////////////////////
// Litmus test for lack of intra-callback ordering of instrs
// 
// core 0     onMiss_X onE_X  onWB_X
// Wcb X 1    (0)      ()     W A 1
//                            R B
//
// core 1     onMiss_Y onE_Y  onWB_Y
// Wcb Y 1    (0)      ()     W B 1
//                            R A

// Allowed Outcome: R A = 0, R B = 0

one sig X, Y, A, B extends Address {}

fact addr_info {
  X.addrType = SharedMorph
  Y.addrType = SharedMorph
  A.addrType = Regular
  B.addrType = Regular
}

// A, B initialization
one sig InitA, InitB in MemoryEvent {}

fact init {
  InitA in Write
  InitA.address = A
  InitA.wval = Zero

  InitB in Write
  InitB.address = B
  InitB.wval = Zero

  InitA in InitialEvent
  InitB in InitialEvent
  all e: Event | e in InitialEvent implies e = InitA or e = InitB
}

// main program instructions
one sig WcbX     in CallbackMemEvent {}
one sig WcbY     in CallbackMemEvent {}

fact core0 {
  // address bindings
  WcbX in WriteCB
  WcbX.address = X
  WcbX.wval = One

  // only these events in this thread
  all e: Event | (WcbX->e in thd) implies e = WcbX
}

fact core1 {
  // address bindings
  WcbY in WriteCB
  WcbY.address = Y
  WcbY.wval = One
  
  // only these events in this thread
  all e: Event | (WcbY->e in thd) implies e = WcbY
}

fact onmiss_x {
  // Ms -> Me
  all ms : MissStart |
    ms.address = X implies
    (all e: Event | (ms->e in thd) implies e = ms or (
      e in MissEnd and (e <: MissEnd).val = Zero
    ))
}

fact onevict_x {
  // Es -> Ee
  all es : EvictStart |
    (es.address = X and es.dirty = Clean) implies 
    (all e: Event | (es->e in thd) implies e = es or (
      e in EvictEnd
    ))
}

fact onwb_x {
  // Es -> W A 1 -> R B -> Ee
  all es : EvictStart | 
    (es.address = X and es.dirty = Dirty) implies 
    (some wa : Write | (
      wa.address = A and
      wa.wval = One and
      (es->wa in sb) and 
      (some rb : Read | (
        rb.address = B and
        wa->rb in sb and
        (all e: Event | (es->e in thd) implies e = es or e = wa or e = rb or (
          e in EvictEnd and
          wa->e in sb
        ))
      ))
    ))
}

fact onmiss_y {
  // Ms -> Me
  all ms : MissStart |
    ms.address = Y implies
    (all e: Event | (ms->e in thd) implies e = ms or (
      e in MissEnd and (e <: MissEnd).val = Zero
    ))
}

fact onevict_y {
  // Es -> Ee
  all es : EvictStart |
    (es.address = Y and es.dirty = Clean) implies 
    (all e: Event | (es->e in thd) implies e = es or (
      e in EvictEnd
    ))
}

fact onwb_y {
  // Es -> W B 1 -> R A -> Ee
  all es : EvictStart | 
    (es.address = Y and es.dirty = Dirty) implies 
    (some wb : Write | (
      wb.address = B and
      wb.wval = One and
      (es->wb in sb) and 
      (some ra : Read | (
        ra.address = A and
        wb->ra in sb and
        (all e: Event | (es->e in thd) implies e = es or e = wb or e = ra or (
          e in EvictEnd and
          ra->e in sb
        ))
      ))
    ))
}

// only allowable threads are core 0/1, onmiss x/y, onwb x/y, onevict x/y
fact allowed_threads {
  all e : Event |
    e in InitialEvent or
    WcbX->e in thd or
    WcbY->e in thd or
    (some ms: MissStart | (ms.address = X or ms.address = Y) and ms->e in thd) or 
    (some es: EvictStart |(es.address = X or es.address = Y) and es->e in thd)
}

// 2 init, 2 thread 0, 4 msme (x + y), 
// 4 esee (x + y), 4 body of esee (x + y) = 16 total events
run allowed {
  some RB : Read | RB.address = B 
  all RB: Read | RB.address = B implies RB.rval = Zero
  some RA : Read | RA.address = A
  all RA: Read | RA.address = A implies RA.rval = Zero
} for 16 Event