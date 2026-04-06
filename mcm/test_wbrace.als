open tako

////////////////////////////////////////////////////////////////////////////////
// Litmus test for Flush Utility
// 
// thread 0   onMiss_X onE_X onWB_X
// RMWcb x 1    ()       ()   W Y 1
// R Y
// demonstrate that program is racy

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
one sig RMWcbX in CallbackMemEvent {}
one sig RY     in MemoryEvent {}


fact thread0 {
  // address bindings
  RMWcbX in RMWCB
  RMWcbX.address = X


  RY in Read
  RY.address = Y

  RMWcbX->RY in sb
  // only these events in this thread
  all e: Event | (RMWcbX->e in thd) implies e = RMWcbX or e = RY
}


fact onmiss_x {
  // Ms -> Me
  all ms : MissStart |
    ms.address = X and
    (all e: Event | (ms->e in thd) implies e = ms or (
      e in MissEnd and (e <: MissEnd).val = Zero
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

// only allowable threads are thread 0, onmiss x, onwb x, onevict x
fact allowed_threads {
  all e : Event |
    e in InitialEvent or
    RMWcbX->e in thd or
    (some ms: MissStart | ms->e in thd) or 
    (some es: EvictStart | es->e in thd)
}


run race {
  some e1, e2: Event | e1->e2 in race
} for 9 Event