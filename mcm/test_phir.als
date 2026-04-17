open tako

////////////////////////////////////////////////////////////////////////////////
// Litmus test for Flush Utility (multi-threaded version)
// 
// core 0     core 1     onMiss_X onE_X onWB_X
// RMWcb X 1  RMWcb X 2  (0)      ()    r3 = R Y
// Fl X       Fl X                      if r3 = 0 then W Y 1 else W Z 2
// R Y        R Z

// Program is racy: after flush in core 1, RMWcb + eviction in core 0 can
// cause race between read and write of Z

one sig X, Y, Z extends Address {}

fact addr_info {
  X.addrType = SharedMorph
  Y.addrType = Regular
  Z.addrType = Regular
}

// y initialization
one sig InitY  in MemoryEvent {}
one sig InitZ  in MemoryEvent {}

fact init {
  InitY in Write
  InitY.address = Y
  InitY.wval = Zero

  InitZ in Write
  InitZ.address = Z
  InitZ.wval = Zero

  InitY in InitialEvent
  InitZ in InitialEvent
  
  all e: Event | e in InitialEvent implies (e = InitY or e = InitZ)
}

// main program instructions
one sig RMWcbX1 in CallbackMemEvent {}
one sig FlX1    in Flush {}
one sig RY      in MemoryEvent {}

one sig RMWcbX2 in CallbackMemEvent {}
one sig FlX2    in Flush {}
one sig RZ      in MemoryEvent {}


fact core0 {
  // address bindings
  RMWcbX1 in RMWCB
  RMWcbX1.address = X
  RMWcbX1.wval = One

  FlX1.address = X

  RY in Read
  RY.address = Y

  RMWcbX1->FlX1 in sb
  FlX1->RY in sb
  // only these events in this thread
  all e: Event | (RMWcbX1->e in thd) implies e = RMWcbX1 or e = FlX1 or e = RY
}

fact core1 {
  // address bindings
  RMWcbX2 in RMWCB
  RMWcbX2.address = X
  RMWcbX2.wval = Two

  FlX2.address = X

  RZ in Read
  RZ.address = Z

  RMWcbX2->FlX2 in sb
  FlX2->RZ in sb
  // only these events in this thread
  all e: Event | (RMWcbX2->e in thd) implies e = RMWcbX2 or e = FlX2 or e = RZ
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
  // Es -> R Y 0 -> W Y 1 -> Ee
  // OR 
  // Es -> R Y !0 -> W Z 2 -> Ee
  all es : EvictStart |
    es.dirty = Dirty implies 
    (es.address = X and
    (some ry : Read | (
      ry.address = Y and
      (es->ry in sb) and
      (ry.rval = Zero implies (
        some wy : Write | (
          wy.address = Y and
          wy.wval = One and
          (ry->wy in sb) and
          (all e: Event | (es->e in thd) implies e = es or e = ry or e = wy or (
            e in EvictEnd and
            wy->e in sb
          ))
        )
      )) and
      (ry.rval != Zero implies (
        some wz : Write | (
          wz.address = Z and
          wz.wval = Two and
          (ry->wz in sb) and
          (all e: Event | (es->e in thd) implies e = es or e = ry or e = wz or (
            e in EvictEnd and
            wz->e in sb
          ))
        )
      ))
    )))
}

// only allowable threads are core0/1, onmiss x, onwb x, onevict x
fact allowed_threads {
  all e : Event |
    e in InitialEvent or
    RMWcbX1->e in thd or
    RMWcbX2->e in thd or
    (some ms: MissStart | ms->e in thd) or 
    (some es: EvictStart | es->e in thd)
}

// 2 init, 6 thread, 4 MsMe (2x) 4 EsEe (2x), 4 onwb events = 20

run allowed1 {
  RY.rval = One
  RZ.rval = Zero
} for 20 Event

run allowed2 {
  RY.rval = One
  RZ.rval = Two
} for 20 Event


run race {
  some e1, e2: Event | e1->e2 in race
} for 20 Event

run forbidden {
  RY.rval = Zero
} for 20 Event