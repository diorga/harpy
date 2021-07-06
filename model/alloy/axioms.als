module axioms
open exec_F


/*
 * Helper functions
 */

// Make a x86-TSO fence
fun mkfence[e:PTag->E, X:Exec_F] : E->E {  
  ^(sb[e,X]) . (stor[CpuFence[e,X]]) . ^(sb[e,X])
}

// Make a FPGA single-channel fence
fun mk_fpga_single_fence[e:PTag->E, X:Exec_F] : E->E {  
  ^(stor[WrRsp[e,X]] ) . ^(sch[e,X] & sb[e,X]) . (stor[FnRsp[e,X]]) . ^(sb[e,X]) .  (stor[EV[e,X]-RdRsp[e,X]])
// JW: ^(stor[WrRsp[e,X]] ) is the same as (stor[WrRsp[e,X]] ). The transitive closure doesn't do anything here.
}

// Make a FPGA any-channel fence
fun mk_fpga_any_fence[e:PTag->E, X:Exec_F] : E->E {  
  ^(stor[WrRsp[e,X]]) . ^(sb[e,X]) . (stor[FnRspAny[e,X]]) . ^(sb[e,X]) .  (stor[EV[e,X]-RdRsp[e,X]])
}

// program order restricted to the same memory location
fun po_loc[e:PTag->E, X:Exec_F] : E->E {
  sb[e,X] & sloc[e,X]
}



// Communication
fun com[e:PTag->E, X:Exec_F] : E->E {
  co[e,X] + rf[e,X] + fr[e,X]
}

// Read-from external
fun rfe[e:PTag->E, X:Exec_F] : E->E {
  rf[e,X] - sthd[e,X] 
}

// From-read external
fun fre[e:PTag->E, X:Exec_F] : E->E {
  fr[e,X] - sthd[e,X] 
}

// ppo for sc
fun ppo_sc[e:PTag->E, X:Exec_F] : E->E {
  sb[e,X] 
}

// ppo for tso
fun ppo_tso[e:PTag->E, X:Exec_F] : E->E {
 ( (sb[e,X]  - (CpuWrite[e,X] -> CpuRead[e,X]) ) & (EV_C[e,X] -> EV_C[e,X]) )
}

// ppo for fpga
fun ppo_fpga[e:PTag->E, X:Exec_F] : E->E {
 ( sb[e,X]  & sch[e,X]  & (  (RdRsp[e,X] + WrRsp[e,X] +FnRsp[e,X] + FnRspAny[e,X]) ->  (EV_F[e,X] - RdRsp[e,X]) ) ) + readpair[e,X] + writepair[e,X] + fencepair[e,X] + fenceanypair[e,X]
}



// prop for sc
fun prop_sc[e:PTag->E, X:Exec_F] : E->E {
   ppo_sc[e,X] + rf[e,X] + fr[e,X] 
}

// prop for tso
fun prop_tso[e:PTag->E, X:Exec_F] : E->E {
   ppo_tso[e,X] + rf[e,X] + fre[e,X] 
}

/*
 * Axioms for the CPU
 *
 */



fun po_loc_cpu[e:PTag->E, X:Exec_F] : E->E {
  (sb[e,X] & sloc[e,X] & (EV_C[e,X] -> EV_C[e,X]) )
}

fun sb_cpu[e:PTag->E, X:Exec_F] : E->E {
  sb[e,X] & (EV_C[e,X] -> EV_C[e,X])
}
fun rf_cpu[e:PTag->E, X:Exec_F] : E->E {
  rf[e,X] & (EV_C[e,X] -> EV_C[e,X])
}
fun fr_cpu[e:PTag->E, X:Exec_F] : E->E {
  fr[e,X] & (EV_C[e,X] -> EV_C[e,X])
}
fun rfe_cpu[e:PTag->E, X:Exec_F] : E->E {
  rfe[e,X] & (EV_C[e,X] -> EV_C[e,X])
}
fun co_cpu[e:PTag->E, X:Exec_F] : E->E {
  co[e,X] & (EV_C[e,X] -> EV_C[e,X])
}

fun po_loc_sch[e:PTag->E, X:Exec_F] : E->E {
  sb[e,X] & sloc[e,X] & sch[e,X]  
}

pred sc_per_loc[e:PTag->E, X:Exec_F] {
  is_acyclic[ po_loc_cpu[e,X] + rf_cpu[e,X] + fr_cpu[e,X] + co_cpu[e,X] ]
// JW: should the second rf_cpu be co_cpu?
}

pred propagation[e:PTag->E, X:Exec_F] {
//is_acyclic[ mkfence[e,X] + ppo_tso[e,X] + rfe_cpu[e,X] + fr_cpu[e,X] + co_cpu[e,X] ] 
  is_acyclic[ mkfence[e,X] + ppo_tso[e,X] + ppo_fpga[e,X] + mk_fpga_single_fence[e,X] 
    + mk_fpga_any_fence[e,X] 
    + rfe[e,X]  + fre[e,X] + co[e,X] ] 
}

// Axioms for SC on the CPU
// Eventually I just used the cat files from heard
pred axioms_sc [e:PTag->E, X:Exec_F] {
  is_acyclic[ sb_cpu[e,X] + rf_cpu[e,X] + fr_cpu[e,X] + co_cpu[e,X] ]
}

// Axioms for TSO on the CPU
pred axioms_tso [e:PTag->E, X:Exec_F] {
  sc_per_loc[e,X]
  propagation[e,X]
}


/*
 * Axioms for the FPGA
 */

// Consistency per same channel
pred sc_per_loc_sch [e:PTag->E, X:Exec_F] {
 let po_loc_sch = sb[e,X] & sloc[e,X] & sch[e,X] + po_loc_cpu[e,X]   |
// JW: Note that there's also a top-level definition called po_loc_sch -- might be confusing?
   is_acyclic[po_loc_sch + com[e,X]]
}

// General axioms, mostly consistency
pred general_axioms[e:PTag->E, X:Exec_F] {
  is_irr[ (fr[e, X]) . (po_loc_sch[e,X]) . (readpair[e,X]) ]
//  is_irr[ (po_loc_sch[e,X]) . (rf[e, X])]
//  is_irr[ (po_loc_sch[e,X]) .(fr[e,X]) . (rf[e, X])]
//  is_irr[ po_loc_cpu[e,X] . (fr[e, X]) . (rf[e, X])]
//  is_irr[po_loc_sch[e,X] . (co[e,X])]
//  is_irr[ (fr[e,X] & (EV_F[e,X] -> EV_C[e,X])) . (rf[e,X]& (EV_C[e,X] -> EV_F[e,X])) . (po_loc_sch[e,X]) ]
  is_irr[ (fre[e,X]) . (rfe[e,X]) . (po_loc_sch[e,X]) ]

  // New axioms
  is_irr[ (rf[e,X]) . (po_loc[e,X])  ]
 // is_irr[ (rf[e,X]) . (sb[e,X]) . (co[e,X]) ]
  // New trace  
 is_irr[ (fr[e,X]) . ( stor[WrRsp[e,X]] ) . ( (sb[e,X]) & (sch[e,X]) ) . (stor[FnRsp[e,X]]) . (sb[e,X]) . (stor[RdReq[e,X]]) . (readpair[e,X]) ]

}

// A fence response guarantees that all preceeding write requests have been answered
pred fence_response [e:PTag->E, X:Exec_F] {
   is_irr[ (sb[e,X]) . (fenceanypair[e,X]) . (sb[e,X]) . ~(writepair[e,X])  ]
   is_irr[ (sb[e,X] & sch[e,X]) . (fencepair[e,X]) . (sb[e,X] & sch[e,X]) . ~(writepair[e,X])  ]
}

// A fence will block other writes until all proceding ones have finished processing
pred fence_block [e:PTag->E, X:Exec_F] {
  is_irr[ (sb[e,X]) . (writepair[e,X]) . (sb[e,X]) . ~(fenceanypair[e,X]) ]
  is_irr[ (sb[e,X]) . (writepair[e,X]) . (sb[e,X]) . ~(fencepair[e,X]) ]
// JW: Just to check: in the second line you don't have "& sch" like in the fence_response axiom -- is that right?
}

// A fence will make the CPU see everything
pred fence_cpu [e:PTag->E, X:Exec_F] {
 // is_irr[ (fr[e,X]) . (sb[e,X]) . (fenceanypair[e,X]) . (sb[e,X]) . (rf[e,X]) . (sb[e,X]) ]
//  is_irr[ (fr[e,X]) . (sb[e,X] & sch[e,X]) . (fencepair[e,X]) . (sb[e,X]) . (rf[e,X]) . (sb[e,X]) ]
// JW: The second line has (sb&sch) before the fencepair, but only (sb) after the fencepair.
// Should it be (sb&sch) after the fencepair too? Looks a bit asymmetric at the moment.
}

pred axioms_fpga [e:PTag->E, X:Exec_F] {
//  sc_per_loc_sch[e, X]
  general_axioms[e, X]
  fence_response[e, X]
  fence_block[e,X]
  fence_cpu[e,X]
}




/*
 * Executions 
 */
pred execution_all [X:Exec_F] {

  E in X.EV

  axioms_tso[none->none, X]
  axioms_fpga[none->none,X]
//  axioms_sc[X]

  // A single FPGA 
  (X.EV_F -> X.EV_F) in X.sthd

  // A single CPU
  //(X.EV_C -> X.EV_C) in X.sthd

}

pred execution_cpu [X:Exec_F] {

  E in X.EV_C

  axioms_tso[none->none, X]
//  axioms_sc[none->none, X]

}

pred execution_fpga [X:Exec_F] {

  E in X.EV_F

  axioms_fpga[none->none, X]

}


run execution_all for 1 Exec_F, exactly 4 E
run execution_fpga for 1 Exec_F, exactly 4 E
run execution_cpu for 1 Exec_F, exactly 4 E

// JW: This predicate holds exactly when the execution X is consistent with our memory model
pred consistent [e:PTag->E, X:Exec_F] {
  axioms_fpga[e, X]
  axioms_tso[e, X]
}
// Allowed
pred page1_ex9[X:Exec_F] {
//  consistent[none->none, X]
  some disj E5, E4,E3, E2, E1, E0 : E {
  X.WrReq = E0 + E1
  X.WrRsp = E2 + E3
  X.RdRsp = E4
  X.RdReq = E5

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) in X.sb
  (E0->E3) + (E1->E2) in X.writepair
  (E2->E4) in X.rf
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  }
}

// JW: This command will search for "interesting" executions. If you run this command 
// lots of times, gradually increasing the event count, then you should get Alloy to spit out
// lots of interesting executions to test on the Harp.
run { 
  some X : Exec_F { 

    // execution X is not consistent ...
    not (consistent[none->none, X])

    // ... but if you remove from X any single event e, then it becomes consistent. 
    // (In other words: every event that appears in X is *important*.)
     all e : X.EV | consistent[rm_EV->e, X]
    page1_ex9[ X]

  } 
} for 1 Exec_F, exactly 4 E

// JW: There exist executions that are allowed by TSO but disallowed by SC... 
run { 
  some X : Exec_F { 
    axioms_tso[none->none, X] 
    not (axioms_sc[none->none, X]) 
  } 
} for 1 Exec_F, 4 E expect 1

// JW: ... but if there is only one CPU thread, then the two models are indistinguishable (at least up to 6 events) 
run {
  some X : Exec_F { 
    axioms_tso[none->none, X] 
    not (axioms_sc[none->none, X])  
    X.EV_C -> X.EV_C in X.sthd 
  }
} for 1 Exec_F, 6 E expect 0 // CAUTION: this takes about 11 seconds using the "glucose" solver

