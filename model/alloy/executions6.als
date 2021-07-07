module executions
open axioms

/*
pred execution_all [X:Exec_F] {
  E in X.EV

  not(consistent[none->none, X])

  X.EV_F -> X.EV_F in X.sthd
  X.EV_C -> X.EV_C  in X.sthd



  some X.RdReq + X.CpuRead // At least a read
}

run execution_all for 1 Exec_F,  exactly 5 E */ 

//run { 
//  some X : Exec_F { 
//   E in X.EV

//    X.EV_F -> X.EV_F in X.sthd
//    some X.RdRsp + X.CpuRead
    // execution X is not consistent ...
//    not (consistent[none->none, X])

    // ... but if you remove from X any single event e, then it becomes consistent. 
    // (In other words: every event that appears in X is *important*.)
//     all e : X.EV | consistent[rm_EV->e, X]
//  } 
//} for 1 Exec_F, exactly 4 E

// JW: This command will search for "interesting" executions. If you run this command 
// lots of times, gradually increasing the event count, then you should get Alloy to spit out
// lots of interesting executions to test on the Harp.


run { 
  some X : Exec_F { 


   E in X.EV
    // execution X is not consistent ...
    not (consistent[none->none, X])


  X.EV_F -> X.EV_F in X.sthd
//  X.EV_C -> X.EV_C  in X.sthd
  
  some X.EV_F
  some X.RdRsp + X.CpuRead


    // ... but if you remove from X any single event e, then it becomes consistent. 
    // (In other words: every event that appears in X is *important*.)
    all e : X.EV | consistent[rm_EV->e, X]

  } 
} for 1 Exec_F, exactly 6 E 




