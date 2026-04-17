open tako

////////////////////////////////////////////////////////////////////////////////
// Litmus Test: Message Passing (MP) with RMWcb as synchronization
// 
// core 0      core 1      OnMiss Y  OnE/WB Y
// W X 1       RMWcb Y 1   (0)       ()
// RMWcb Y 1   R X

// Forbidden Outcome: RMWcb Y = 1, R X = 0

one sig X, Y extends Address {}

fact addr_info {
  X.addrType = Regular
  Y.addrType = SharedMorph
}

// y initialization
one sig InitX  in MemoryEvent {}

fact init {
  InitX in Write
  InitX.address = X
  InitX.wval = Zero
  
  InitX in InitialEvent
  all e: Event | e in InitialEvent implies e = InitX
}

// main program instructions
one sig WX       in MemoryEvent {}
one sig RMWCBY1  in CallbackMemEvent {}
one sig RMWCBY2  in CallbackMemEvent {}
one sig RX       in MemoryEvent {}


fact core0 {
  // address bindings
  WX in Write
  WX.address = X
  WX.wval = One

  RMWCBY1 in RMWCB
  RMWCBY1.address = Y
  RMWCBY1.wval = One

  WX->RMWCBY1 in sb
  // only these events in this thread
  all e: Event | (WX->e in thd) implies e = WX or e = RMWCBY1
}

fact core1 {
  // address bindings
  RMWCBY2 in RMWCB
  RMWCBY2.address = Y
  RMWCBY2.wval = One
  
  RX in Read
  RX.address = X

  RMWCBY2->RX in sb
  // only these events in this thread
  all e: Event | (RMWCBY2->e in thd) implies e = RMWCBY2 or e = RX
}

fact onmiss_y {
  // Ms -> Me
  all ms : MissStart |
    ms.address = Y and
    (all e: Event | (ms->e in thd) implies e = ms or (
      e in MissEnd and (e <: MissEnd).val = Zero
    ))
}

fact onevict_wb_y {
  // Es -> Ee
  all es : EvictStart |
    (es.address = Y and
    (all e: Event | (es->e in thd) implies e = es or (
      e in EvictEnd
    )))
}

// only allowable threads are core 0, 1, onmiss y, onwb y, onevict y
fact allowed_threads {
  all e : Event |
    e in InitialEvent or
    WX->e in thd or
    RMWCBY2->e in thd or
    (some ms: MissStart | ms->e in thd) or 
    (some es: EvictStart | es->e in thd)
}

run allowed {
  RMWCBY2.rval = Zero
  RX.rval = Zero
} for 13 Event

run forbidden {
  RMWCBY2.rval = One
  RX.rval = Zero
} for 13 Event