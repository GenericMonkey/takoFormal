open tako

////////////////////////////////////////////////////////////////////////////////
// Litmus Test: Message Passing (MP)
// 
// core 0      core 1
// W X 1       RMW Y 1
// RMW Y 1     R X

// Forbidden Outcome: R Y = 1, R X = 0

one sig X, Y extends Address {}

fact addr_info {
  X.addrType = Regular
  Y.addrType = Regular
}

// y initialization
one sig InitX  in MemoryEvent {}
one sig InitY  in MemoryEvent {}

fact init {
  InitX in Write
  InitX.address = X
  InitX.wval = Zero
  
  InitY in Write
  InitY.address = Y
  InitY.wval = Zero

  InitX in InitialEvent
  InitY in InitialEvent
  all e: Event | e in InitialEvent implies e = InitX or e = InitY
}

// main program instructions
one sig WX     in MemoryEvent {}
one sig RMWY1  in MemoryEvent {}
one sig RMWY2  in MemoryEvent {}
one sig RX     in MemoryEvent {}


fact core0 {
  // address bindings
  WX in Write
  WX.address = X
  WX.wval = One

  RMWY1 in RMW
  RMWY1.address = Y
  RMWY1.wval = One

  WX->RMWY1 in sb
  // only these events in this thread
  all e: Event | (WX->e in thd) implies e = WX or e = RMWY1
}

fact core1 {
  // address bindings
  RMWY2 in RMW
  RMWY2.address = Y
  RMWY2.wval = One
  
  RX in Read
  RX.address = X

  RMWY2->RX in sb
  // only these events in this thread
  all e: Event | (RMWY2->e in thd) implies e = RMWY2 or e = RX
}

// only allowable threads are core 0, and core 1
fact allowed_threads {
  all e : Event |
    e in InitialEvent or
    WX->e in thd or
    RMWY2->e in thd
}

run forbidden {
  RMWY2.rval = One
  RX.rval = Zero
} for 6 Event