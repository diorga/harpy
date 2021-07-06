module exec_F
open relations[E]
sig E {}

sig Exec_F  {

  // FPGA specific elements 
  EV_F : set E,                                                                                                     // domain of all FPGA events
  WrReq, WrRsp, RdReq, RdRsp, FnReq, FnRsp, FnReqAny,FnRspAny : set E,     // set all FPGA events,
  sch  : E->E,                                                                                                       // same channel
  readpair, writepair, fencepair, fenceanypair : E->E,                                                  // basically same mdata

  // CPU-only elements
  EV_C : set E,                                                                                                    // domain of all CPU events
  CpuWrite, CpuRead, CpuFence : set E,                                                       // set all CPU events
 
  // common relations 
  EV: set E,
  sthd : E->E,                                                                                                       // same thread (partial E.R.)
  rf : E->E,                                                                                                            // reads-from
  sb : E->E,                                                                                                          // sequance before
  sloc : E->E,                                                                                                       // same location (partial E.R.)
  co : E -> E,                                                                                                         // coherence order

  // Derived relations
  fr  : E -> E                                                                                                           // from-read     
} {

  // EV_F captures all FPGA events
  WrReq + WrRsp + RdReq + RdRsp + FnReq + FnRsp + FnReqAny + FnRspAny  = EV_F
  
  // EV_C captures all CPU events
  CpuWrite + CpuRead + CpuFence = EV_C

  // EV captures all event
  EV = EV_F + EV_C

  // you can read if it is from the same location
  rf in sloc

   // sequenced-before is intra-thread
  sb in sthd

  // sequance-before is also total within a thread
  sthd in *sb + ~*sb

  // sfpga is an equivalence relation among events
  is_equivalence[sthd, EV]

 // loc is an equivalence relation among reads and writes
  is_equivalence[sloc, RdReq + RdRsp+ WrReq +  WrRsp + CpuRead + CpuWrite]

  // Simplification that you can only have a single event at a time
  disj[WrReq, WrRsp, RdReq, RdRsp, FnReq, FnRsp, FnReqAny, FnRspAny, CpuWrite, CpuRead, CpuFence]

  // sequenced-before is acyclic and transitive
  strict_partial_order[sb]

  // same channel is symetric, transitive
  is_equivalence[sch, EV_F]

  // pairs on go in corresponding events
  readpair in RdReq one -> one RdRsp
  writepair in WrReq one -> one WrRsp
  fencepair in FnReq one -> one FnRsp
  fenceanypair in FnReqAny one -> one FnRspAny

  RdReq in dom[readpair]  
  WrReq in dom[writepair]
  FnReq in dom[fencepair]
  FnReqAny in dom[fenceanypair]
  
  readpair in sb & sch & sloc
  writepair in sb & sch & sloc
  fencepair in sb & sch
  fenceanypair in sb

  // co is acyclic and transitive
  strict_partial_order[co]

  // co is a union, over all locations x, of strict
  // total orders on writes to x
  (co + ~co) = ((CpuWrite + WrRsp) -> (CpuWrite + WrRsp)) & sloc - iden

  // rf connects each read to at most one write
  rf in (CpuWrite + WrRsp) lone -> (CpuRead + RdRsp)

  // This should just be the definition of the fr relation
   fr =  (((RdRsp + CpuRead) -> (WrRsp + CpuWrite)) & sloc) - (~rf . *~co)
 
  // sthd does not connect an FPGA event and a CPU event
  disj[sthd , (EV_C->EV_F)] 

  // Make sure there is a single co edge
  all e1, e2, e3 : EV | not ((e1 -> e2) in co and (e2 -> e3) in co)
 

}

// Perturbation Tags are an idea due to Daniel Lustig et al.
// (ASPLOS'17, http://dl.acm.org/citation.cfm?id=3037723)
abstract sig PTag {}
one sig rm_EV extends PTag {}

fun rm_EV_pair[e:PTag->E, X:Exec_F] : set E {
  e[rm_EV] + 
  e[rm_EV].(X.writepair) + (X.writepair).(e[rm_EV]) + 
  e[rm_EV].(X.readpair) + (X.readpair).(e[rm_EV]) +
  e[rm_EV].(X.fencepair) + (X.fencepair).(e[rm_EV]) +
  e[rm_EV].(X.fenceanypair) + (X.fenceanypair).(e[rm_EV]) 
}

fun rm_EV_rel[e:PTag->E, r:E->E, X:Exec_F] : E->E {
  (univ - rm_EV_pair[e,X]) <: r :> (univ - rm_EV_pair[e,X])
}



// Apply perturbations to each set. For instance, FnReq[e,X] refers to the set of
// FnReq events in the execution obtained by removing e from X. (Note that we
// are relying on Alloy's type system to disambiguate the two distinct uses of 
// "FnReq" here, because one takes one argument and the other takes two.)
fun EV [e:PTag->E, X:Exec_F] : set E { X.EV - rm_EV_pair[e,X] }
fun EV_F [e:PTag->E, X:Exec_F] : set E { X.EV_F - rm_EV_pair[e,X]  }
fun WrReq [e:PTag->E, X:Exec_F] : set E { X.WrReq - rm_EV_pair[e,X] }
fun WrRsp [e:PTag->E, X:Exec_F] : set E { X.WrRsp - rm_EV_pair[e,X]  }
fun RdReq [e:PTag->E, X:Exec_F] : set E { X.RdReq - rm_EV_pair[e,X]  }
fun RdRsp [e:PTag->E, X:Exec_F] : set E { X.RdRsp - rm_EV_pair[e,X]   }
fun FnReq [e:PTag->E, X:Exec_F] : set E { X.FnReq - rm_EV_pair[e,X]  }
fun FnRsp [e:PTag->E, X:Exec_F] : set E { X.FnRsp - rm_EV_pair[e,X]    }
fun FnReqAny [e:PTag->E, X:Exec_F] : set E { X.FnReqAny - rm_EV_pair[e,X]   }
fun FnRspAny [e:PTag->E, X:Exec_F] : set E { X.FnRspAny -rm_EV_pair[e,X]    }

fun EV_C [e:PTag->E, X:Exec_F] : set E { X.EV_C - rm_EV_pair[e,X]  }
fun CpuWrite [e:PTag->E, X:Exec_F] : set E { X.CpuWrite - rm_EV_pair[e,X]  }
fun CpuRead [e:PTag->E, X:Exec_F] : set E { X.CpuRead - rm_EV_pair[e,X]  }
fun CpuFence [e:PTag->E, X:Exec_F] : set E { X.CpuFence - rm_EV_pair[e,X]  }

// Apply perturbations to each relation.
fun sb [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.sb, X  ] }
fun sch [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.sch, X] }
fun readpair [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.readpair, X] }
fun writepair [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.writepair, X] }
fun fencepair [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.fencepair, X] }
fun fenceanypair [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.fenceanypair, X] }
fun sthd [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.sthd, X] }
fun rf [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.rf, X] }
fun sloc [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.sloc, X] }
fun co [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.co, X] }
fun fr [e:PTag->E, X:Exec_F] : E->E { rm_EV_rel[e, X.fr, X] }

// A CPU-FPGA execution with no constraints
pred free_execution_all [X:Exec_F] {

  E in X.EV

  // A single FPGA 
  (X.EV_F -> X.EV_F) in X.sthd

  // A single CPU
  (X.EV_C -> X.EV_C) in X.sthd

}

// A CPU execution with no constraints
pred free_execution_cpu [X:Exec_F] {

  E in X.EV_C
  E in X.CpuWrite + X.CpuRead + X.CpuFence

}

// A FPGA execution with no constraints
pred free_execution_fpga [X:Exec_F] {

  E in X.EV_F

  // A single FPGA 
  (X.EV_F -> X.EV_F) in X.sthd

  some WrRsp
  no RdReq
  no RdRsp
  no  FnReq
  no FnRsp
  no FnReqAny
  no FnRspAny 

}


run free_execution_all for 1 Exec_F, exactly 8 E
run free_execution_fpga for 1 Exec_F, exactly 4 E
run free_execution_cpu for 1 Exec_F, exactly 4 E




