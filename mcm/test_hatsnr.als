open tako

////////////////////////////////////////////////////////////////////////////////
// Litmus test for HATS (No Race)
// 
// thread 0        onMiss E       onEvict/WB E
// RMWcb E 1        r2 = R G        if E != 1:
// Flush E          if r2 != 1        W L 1
// R L                W G 1
//                    ret 0
//                  else
//                    ret 1
// Forbidden Outcome: RMWcb E = 1, R L = 0
// Forbidden Outcome: RMWcb E = 0, R L = 1
// Allowed Outcome:   RMWcb E = 1, R L = 1
// Allowed Outcome:   RMWcb E = 0, R L = 0

one sig E, L, G extends Address {}

fact addr_info {
  E.addrType = SharedMorph
  L.addrType = Regular
  G.addrType = Regular
}

// L, G initialization
one sig InitL in MemoryEvent {}
one sig InitG in MemoryEvent {}

fact init {
  InitL in Write
  InitL.address = L
  InitL.wval = Zero

  InitG in Write
  InitG.address = G
  InitG.wval = Zero

  InitL in InitialEvent
  InitG in InitialEvent
  all e: Event | e in InitialEvent implies e = InitL or e = InitG
}

// main program instructions
one sig RMWcbE in CallbackMemEvent {}
one sig FlE    in Flush {}
one sig RL     in MemoryEvent {}

fact thread0 {
  // address bindings
  RMWcbE in RMWCB
  RMWcbE.address = E
  RMWcbE.wval = One

  FlE.address = E

  RL in Read
  RL.address = L

  RMWcbE->FlE in sb
  FlE->RL in sb

  // only these events in this thread
  all e: Event | (RMWcbE->e in thd) implies e = RMWcbE or e = FlE or e = RL
}

fact onmiss_e {
  // Ms -> R G 1 -> Me 1
  // OR 
  // Ms -> R G !1 -> W B 1 -> Me 0
  all ms : MissStart |
    ms.address = E and
    (some rg : Read | (
      rg.address = G and
      (ms->rg in sb) and
      (rg.rval = One implies (
        (all e: Event | (ms->e in thd) implies e = ms or e = rg or (
          e in MissEnd and 
          (e <: MissEnd).val = One and
          rg->e in sb
        ))
      )) and
      (rg.rval != One implies (
        some wg : Write | (
          wg.address = G and
          wg.wval = One and
          (rg->wg in sb) and
          (all e: Event | (ms->e in thd) implies e = ms or e = rg or e = wg or (
            e in MissEnd and
            (e <: MissEnd).val = Zero and
            wg->e in sb
          ))
        )
      ))
    ))
}

fact onevict_owb_e {
  // Es 1 -> Ee
  // OR
  // Es !1 -> W L 1 -> Ee
  all es : EvictStart |
    // covers both clean and dirty
    es.address = E and
    (es.val = One implies (
      (all e: Event | (es->e in thd) implies e = es or (
        e in EvictEnd
      ))
    )) and
    (es.val != One implies (
      some wl : Write | (
        wl.address = L and
        wl.wval = One and
        (es->wl in sb) and
        (all e: Event | (es->e in thd) implies e = es or e = wl or (
          e in EvictEnd and
          wl->e in sb
        ))
      )
    ))
}


// only allowable threads are thread 0, onmiss e, onwb e, onevict e
fact allowed_threads {
  all e : Event |
    e in InitialEvent or
    RMWcbE->e in thd or
    (some ms: MissStart | ms->e in thd) or 
    (some es: EvictStart | es->e in thd)
}

// longest runtime ive seen, about 30 seconds
run no_race {
  some e1, e2: Event | e1->e2 in race
} for 19 Event

run allowed1 {
  RMWcbE.rval = One
  RL.rval = One
} for 19 Event

run allowed2 {
  RMWcbE.rval = Zero
  RL.rval = Zero
} for 19 Event

run forbidden1 {
  RMWcbE.rval = One
  RL.rval = Zero
} for 19 Event

run forbidden2 {
  RMWcbE.rval = Zero
  RL.rval = One
} for 19 Event