open tako

////////////////////////////////////////////////////////////////////////////////
// Litmus Test: Message Passing (MP)
// 
// core 0    core 1
// W X 1     R Y
// W Y 1     R X

// Allowed Outcome: R Y = 1, R X = 0

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
one sig WX  in MemoryEvent {}
one sig WY  in MemoryEvent {}
one sig RY  in MemoryEvent {}
one sig RX  in MemoryEvent {}


fact core0 {
  // address bindings
  WX in Write
  WX.address = X
  WX.wval = One

  WY in Write
  WY.address = Y
  WY.wval = One

  WX->WY in sb
  // only these events in this thread
  all e: Event | (WX->e in thd) implies e = WX or e = WY
}

fact core1 {
  // address bindings
  RY in Read
  RY.address = Y

  RX in Read
  RX.address = X

  RY->RX in sb
  // only these events in this thread
  all e: Event | (RY->e in thd) implies e = RY or e = RX
}

// only allowable threads are core 0, and core 1
fact allowed_threads {
  all e : Event |
    e in InitialEvent or
    WX->e in thd or
    RY->e in thd
}

run allowed {
  RY.rval = One
  RX.rval = Zero
} for 6 Event