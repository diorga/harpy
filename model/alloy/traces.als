module traces
open exec_F
open axioms

// Allowed under TSO, 
// Disallowed under SC
pred store_buffering[X:Exec_F] {
  consistent[none->none, X]
  some disj E3,E2,E1,E0 : E {
    X.CpuFence = none
    X.CpuRead = E3+E1
    X.CpuWrite = E2+E0
    X.EV_C = E3+E2+E1+E0

    X.fr = (E3->E0)+(E1->E2)
    X.sloc = sq[E0+E3] + sq[E1+E2]
    X.sthd = sq[E0+E1] + sq[E2+E3]
    X.sb = (E0->E1)+(E2->E3)
  }
}



// Allowed
pred page1_ex1[X:Exec_F] {
  consistent[none->none, X]
  some disj E3, E2, E1, E0 : E {
  X.WrReq = E0
  X.WrRsp = E1
  X.RdRsp = E2
  X.RdReq = E3

  (E0->E1) + (E1->E2) in X.sb
  (E2->E1) in X.fr
  X.sch = sq[E0 + E1 + E2 + E3]
  X.sloc = sq[E0+ E1 + E2 + E3]
  }
}

// Disallowed
pred page1_ex2[X:Exec_F] {
  consistent[none->none, X]
  some disj E3, E2, E1, E0 : E {
  X.WrReq = E0
  X.WrRsp = E2
  X.RdRsp = E1
  X.RdReq = E3

  (E0->E1) + (E1->E2) in X.sb
  (E2->E1) in X.rf
  X.sch = sq[E0 + E1 + E2 + E3]
  X.sloc = sq[E0+ E1 + E2 + E3]
  }
}

// Allowed
pred page1_ex3[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {
  X.WrReq = E0
  X.WrRsp = E1
  X.RdRsp = E2 + E3
  X.RdReq = E4 + E5

  (E0->E1) + (E1->E2) + (E2->E3) in X.sb
  (E1->E2) in X.rf
  (E3->E1) in X.fr
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  }
}

// Allowed
pred page1_ex4[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {
  X.WrReq = E0
  X.WrRsp = E1
  X.RdRsp = E2 + E3
  X.RdReq = E4 + E5

  (E0->E1) + (E1->E2) + (E2->E3) in X.sb
  (E1->E3) in X.rf
  (E2->E1) in X.fr
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  }
}

// Disallowed
pred page1_ex5[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {
  X.WrReq = E0
  X.WrRsp = E2
  X.RdRsp = E1 + E3
  X.RdReq = E4 + E5

  (E0->E1) + (E1->E2) + (E2->E3) in X.sb
  (E2->E1) in X.rf
  (E3->E2) in X.fr
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  }
}

// Disallowed
pred page1_ex6[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {
  X.WrReq = E0
  X.WrRsp = E3
  X.RdRsp = E1 + E2
  X.RdReq = E4 + E5

  (E0->E1) + (E1->E2) + (E2->E3) in X.sb
  (E3->E1) in X.rf
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  }
}

// Allowed
pred page1_ex7[X:Exec_F] {
  axioms_fpga[none->none, X]
  some disj E5, E4,E3, E2, E1, E0 : E {
  X.WrReq = E0 + E2
  X.WrRsp = E1 + E3
  X.RdRsp = E4
  X.RdReq = E5

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) in X.sb
  (E0->E1) + (E2->E3) in X.writepair
  (E1->E4) in X.rf
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  }
}

// Allowed
pred page1_ex8[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4,E3, E2, E1, E0 : E {
  X.WrReq = E0 + E1
  X.WrRsp = E2 + E3
  X.RdRsp = E4
  X.RdReq = E5

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) in X.sb
  (E0->E2) + (E1->E3) in X.writepair
  (E2->E4) in X.rf
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  }
}

// Allowed
pred page1_ex9[X:Exec_F] {
  consistent[none->none, X]
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

// Disallowed
pred page1_ex10[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4,E3, E2, E1, E0 : E {
  X.WrReq = E0 + E1
  X.WrRsp = E2 + E4
  X.RdRsp = E3
  X.RdReq = E5

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) in X.sb
  (E0->E2) + (E1->E4) in X.writepair
  (E4->E3) in X.rf
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  }
}

// Disallowed
pred page1_ex11[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {
  X.WrReq = E0 + E1
  X.WrRsp = E2 + E4
  X.RdRsp = E3
  X.RdReq = E5

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) in X.sb
  (E0->E4) + (E1->E2) in X.writepair
  (E4->E3) in X.rf
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  }
}



// Disallowed
pred page2_ex1[X:Exec_F] {
  consistent[none->none, X]
  some disj E3, E2, E1, E0 : E {
  X.WrReq = E0
  X.WrRsp = E1
  X.RdReq = E2
  X.RdRsp = E3

  (E0->E1) + (E1->E2) + (E2->E3) in X.sb
  (E3->E1) in X.fr
  X.sch = sq[E0 + E1 + E2 + E3]
  X.sloc = sq[E0+ E1 + E2 + E3]
  }
}


// Disallowed
pred page2_ex2[X:Exec_F] {
  consistent[none->none, X]
  some disj E3, E2, E1, E0 : E {

  X.RdRsp = E0
  X.WrRsp = E1

  (E0->E1) in X.sb
  (E1->E0) in X.rf
  X.sch = sq[E0 + E1 + E2 + E3]
  X.sloc = sq[E0+ E1 + E2 + E3]
  }
}


// Disallowed
pred page2_ex3[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.CpuWrite = E0 + E1
  X.RdRsp = E2 + E3

  (E0->E1) + (E2->E3) in X.sb
  (E0->E3) + (E1->E2) in X.rf
  X.sch = sq[E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  X.sthd = sq[E0 + E1] + sq[E2 + E3 + E4 + E5]
  }
}


// Disallowed
pred page2_ex4[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.CpuRead = E0 + E1
  X.WrRsp = E2 + E3

  (E0->E1) + (E2->E3) in X.sb
  (E3->E0) + (E2->E1) in X.rf
  X.sch = sq[E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  X.sthd = sq[E0 + E1] + sq[E2 + E3 + E4 + E5]
  }
}

// Disallowed
pred page2_ex5[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.WrRsp = E0 + E1
  X.RdRsp = E2
  X.RdReq = E3

  (E0->E1) + (E0->E3) + (E1->E2) in X.sb
  (E2->E0)  in X.fr
  X.sch = sq[E0 + E1 + E2 + E3 + E4 + E5]
  X.sloc = sq[E0+ E1 + E2 + E3 + E4 + E5]
  X.sthd = sq[E0 + E1 + E2 + E3 + E4 + E5]
  }
}



// Alowed
pred example1[X:Exec_F] {
  consistent[none->none, X]
  some disj E3, E2, E1,E0 : E {
    X.WrReq = E0
    X.WrRsp = E1
    X.RdRsp = E2
    X.RdReq = E3

    (E0->E1) + (E1->E2) in X.sb
    (E2->E1) in X.fr
    X.sloc = sq[E0+ E1 + E2 + E3]
    X.sthd = sq[E0+E1+E2 + E3]

  }
}

// Allowed
pred example2[X:Exec_F] {
  consistent[none->none, X]
  some disj E3, E2, E1, E0 : E {

    X.WrReq = E0
    X.WrRsp = E1
    X.RdRsp = E2
    X.RdReq = E3

    (E0->E1) + (E1->E2) in X.sb
    (E2->E1) in X.fr
    X.sch = sq[E0 + E1 + E2 + E3]
    X.sloc = sq[E0+ E1 + E2 + E3]
    X.sthd = sq[E0 + E1 + E2 + E3]

  }
}

// Disallowed
pred example3_single[X:Exec_F] {
  consistent[none->none, X]
  some disj E5,E4,E3,E2,E1,E0 : E {

    X.WrReq = E0
    X.WrRsp = E4
    X.RdRsp = E3
    X.RdReq = E5
    X.FnReq = E1
    X.FnRsp = E2

    (E0->E1) + (E1->E2) + (E2->E5) + (E2->E3) in X.sb // You do not care when the WrRsp arrives
    (E0->E1) + (E0->E3) in X.sch
    X.fr = (E3->E4)
    (E1->E2) in X.fencepair
    (E0->E3) in X.sloc
    X.sthd = sq[E0+E1+E2+E3+E4 +E5]
  }
}

// Disallowed
pred example3_any[X:Exec_F] {
  consistent[none->none, X]
  some disj E5,E4,E3,E2,E1,E0 : E {

    X.WrReq = E0
    X.WrRsp = E4
    X.RdRsp = E3
    X.RdReq = E5
    X.FnReqAny = E1
    X.FnRspAny = E2

    (E0->E1) + (E1->E2) + (E2->E5) + (E2->E3) in X.sb // You do not care when the WrRsp arrives
    (E0->E3)  in X.sch
    X.fr = (E3->E4)
    (E1->E2) in X.fenceanypair
    (E0->E3) in X.sloc
    X.sthd = sq[E0+E1+E2+E3+E4+E5]
  }
}


// Allowed
pred example4[X:Exec_F] {
   consistent[none->none, X]
  some disj E7,E6,E5,E4,E3,E2,E1,E0 : E {
    X.WrReq = E0 + E1
    X.WrRsp = E4 + E5
    X.RdRsp = E2 + E3
    X.RdReq = E6 + E7

    (E0->E1) + (E1->E2) +  (E2->E3) in X.sb // You do not care when the 2 WrRsp arrive
    (E0->E4) + (E1->E5) in X.writepair
    (E4->E3) + (E5->E2) in X.rf
    (E0->E1) in X.sch
    sq[E0+E1+E2+E3] in X.sloc
    X.sthd = sq[E0+E1+E2+E3+E4+E5+E6+E7]
  }
}

// Allowed
pred example5[X:Exec_F] {
  consistent[none->none, X]
  some disj E7,E6,E5,E4,E3,E2,E1,E0 : E {

    X.WrReq = E0 + E2
    X.WrRsp = E1 + E3
    X.RdRsp = E4 + E5
    X.RdReq = E7 + E6

    (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) + (E4->E5) in X.sb
    (E5->E3) in X.fr
    (E1->E5) + (E3->E4) in X.rf
    sq[E0+E1+E2+E3+E4+E5] in X.sloc
    X.sthd = sq[E0+E1+E2+E3+E4+E5+E6+E7]
  }
}

// Disallowed
pred example6[X:Exec_F] {
  consistent[none->none, X]
  some disj E7,E6,E5,E4,E3,E2,E1,E0 : E {

    X.WrReq = E0 + E2
    X.WrRsp = E1 + E3
    X.RdRsp = E4 + E5
    X.RdReq = E7 + E6

    (E0->E1) + (E1->E2) + (E2->E3) +(E3->E6) +(E3->E7) +(E3->E4) + (E4->E5) in X.sb
    (E5->E3) in X.fr
    (E1->E5) + (E3->E4) in X.rf
    X.sch = sq[E0+E1+E2+E3+E4+E5+E6+E7]
    sq[E0+E1+E2+E3+E4+E5] in X.sloc
    X.sthd = sq[E0+E1+E2+E3+E4+E5+E6+E7]
  }
}

// This barely makes sense. I should eliminate it
pred example7[X:Exec_F] {
  consistent[none->none, X]
  some disj E9, E8, E7, E6, E5, E4, E3, E2, E1, E0 : E {

    X.WrReq = E0 + E2
    X.WrRsp = E8 + E9
    X.RdReq = E3 + E5
    X.RdRsp = E4 + E6
    X.FnReqAny = E1
    X.FnRspAny = E7

    (E0->E1) + (E1->E7) + (E7->E2) + (E2->E3) + (E3->E4) + (E4->E5) + (E5->E6)  in X.sb
    (E0->E8) + (E2->E9) in X.writepair 
    (E3->E4) + (E5->E6) in X.readpair
    (E9->E4) + (E8->E6) in X.rf
    X.sthd = sq[E0+E1+E2+E3+E4+E5+E6+E7+E8+E9]
    sq[E0+E2+E3+E4+E5+E6+E8+E9] in X.sloc
//  sq[E0+E1+E2+E3+E4+E5+E6+E7+E8+E9] in X.sch
  }
}

// Allowed
pred example8[X:Exec_F] {
  consistent[none->none, X]
  some disj E5,E4,E3,E2,E1,E0 : E {

    X.WrReq = E0 + E1
    X.WrRsp = E3 + E4
    X.RdRsp = E2
    X.RdReq = E5

    (E0->E1) + (E1->E2)  in X.sb
    (E0->E3) + (E1->E4) in X.writepair
    (E3->E2)  in X.rf
    (E0->E1) in X.sch
    sq[E0+E1+E2] in X.sloc
    X.sthd = sq[E0+E1+E2+E3+E4+E5]
  }
}

// Disallowed
pred example9[X:Exec_F] {
  consistent[none->none, X]
  some disj E5,E4,E3,E2,E1,E0 : E {

    X.WrReq = E0 + E2
    X.WrRsp = E1 + E3
    X.RdReq = E4
    X.RdRsp = E5


   (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) + (E4->E5)  in X.sb
   (E0->E1) + (E2->E3) in X.writepair
   (E5->E3) in X.fr
   (E1->E5)  in X.rf
    sq[E0+E1+E2+E3+E4+E5] in X.sch
    sq[E0+E1+E2+E3+E4+E5] in X.sloc
    X.sthd = sq[E0+E1+E2+E3+E4+E5]
  }
}


// Allowed
pred example10[X:Exec_F] {
  consistent[none->none, X]
  some disj E3,E2,E1,E0 : E {

    X.WrReq = E0
    X.WrRsp = E2
    X.RdRsp = E1
    X.RdReq = E3

    (E0->E1)  in X.sb
    (E1->E2) in X.fr
    sq[E0+E1] in X.sch
    sq[E0+E1] in X.sloc
    X.sthd = sq[E0+E1+E2+E3]
  }
}

// Disalllowed
pred fence_order_test[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4,E3,E2,E1,E0 : E {

    X.WrReq = E0 + E2
    X.FnReqAny = E1
    X.WrRsp = E3 + E4
    X.FnRspAny = E5


    (E0->E1) + (E1->E2) + (E2->E3)   in X.sb
    (E0->E3) + (E2->E4) in X.writepair
    (E1->E5) in X.fenceanypair
    (E4->E3) in X.sb // This should be prevented by the axiom
    X.sthd = sq[E0+E1+E2 +E3 + E4 +E5]
  }
}


// Allowed
pred cpu_fpga1[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.WrReq = E0 + E2
  X.WrRsp = E1 + E3
  X.CpuRead = E4 + E5

  (E1->E3) + (E4->E5) in X.sb
  X.sthd = sq[E0+E1+E2+E3] + sq[E4+E5]
  (E1->E3) in X.sch
  sq[E0+E1+E2+E3+E4+E5] in X.sloc
  (E1->E4) + (E3->E5) in X.rf
  }
}

// Disallowed
pred cpu_fpga2[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.WrReq = E0 + E2
  X.WrRsp = E1 + E3
  X.CpuRead = E4 + E5

  (E1->E3) + (E4->E5) in X.sb
  X.sthd = sq[E0+E1+E2+E3] + sq[E4+E5]
  (E1->E3) in X.sch
  sq[E0+E1+E2+E3+E4+E5] in X.sloc
 (E1->E5) + (E3->E4) in X.rf
  }
}

// Allowed
pred cpu_fpga3[X:Exec_F] {
  consistent[none->none, X]

  some disj E5, E4, E3, E2, E1, E0 : E {

  X.WrReq = E0 + E2
  X.WrRsp = E1 + E3
  X.CpuRead = E4 + E5

  (E1->E3)  + (E4->E5) in X.sb
  X.sthd = sq[E0+E1+E2+E3] + sq[E4+E5]
  no (X.sch & (E1->E3))
  sq[E0+E1+E2+E3+E4+E5] in X.sloc
 (E1->E5) + (E3->E4) in X.rf
  }
}

// Allowed
pred cpu_fpga4[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.RdReq = E5 + E4 
  X.RdRsp = E0 + E1
  X.CpuWrite = E2 + E3

  (E0->E1) + (E2->E3) in X.sb
  X.sthd = sq[E0+E1+E4+E5] + sq[E2+E3]
  sq[E0+E1+E2+E3] in X.sloc
 (E2->E1) + (E3->E0) in X.rf
  }
}


// Allowed
pred cpu_fpga6[X:Exec_F] {
  consistent[none->none, X]
  some disj E5,E4, E3, E2, E1, E0 : E {

  X.RdReq = E5
  X.RdRsp = E3
  X.WrRsp =E2
  X.CpuWrite = E0
  X.CpuRead = E1
  X.WrReq = E4

  (E0->E1) + (E2->E3)+(E2->E5) in X.sb
  X.sthd = sq[E0+E1] + sq[E2+E3+E4+E5]
  sq[E0+E1+E2+E3+E4+E5] in X.sloc
  (E3->E0) + (E1->E2) in X.fr
  }
}

// Disallowed
pred cpu_fpga7[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.CpuWrite = E0
  X.CpuRead = E1
  X.WrReq = E2
  X.WrRsp =E3
  X.RdReq = E4
  X.RdRsp = E5



  (E0->E1)  + (E2->E3) + (E3->E4) + (E4->E5) in X.sb
  sq[E2+E3+E4+E5] in X.sch
  X.sthd = sq[E0+E1] + sq[E2+E3+E4+E5]
  sq[E0+E1] +sq[E2+E3+E4+E5] in X.sloc
  (E1->E3) + (E5->E0) in X.fr
  }
}


// Disallowed
pred automatic_trace1[X:Exec_F] {
  consistent[none->none, X]
  some disj E3, E2, E1, E0 : E {

  X.WrReq = E0
  X.WrRsp =E3
  X.RdReq = E1
  X.RdRsp = E2

  (E0->E1)  + (E1->E2) + (E2->E3) in X.sb
  X.sthd = sq[E0+E1+E2+E3]
  sq[E0+E1+E2+E3] in X.sloc
  (E3->E2) in X.rf
  }
}

// Disallowed
pred automatic_trace2[X:Exec_F] {
  consistent[none->none, X]
  some disj E3, E2, E1, E0 : E {

  X.CpuWrite = E3
  X.CpuRead = E2
  X.WrReq = E0
  X.WrRsp =E1



  (E0->E1)  + (E2->E3) in X.sb
  sq[E0 +E1] in X.sch
  X.sthd = sq[E0+E1] + sq[E2+E3]
  sq[E0+E1+E2+E3] in X.sloc
  (E1->E2)  in X.rf
  (E3->E1) in X.co
  }
}


//Now it is working
pred fpga_fence_cpu_read[X:Exec_F] {
  consistent[none->none, X]
  some disj E7, E6, E5, E4, E3, E2, E1, E0 : E {

  X.CpuRead = E6 + E7
  X.WrReq = E0 + E4
  X.WrRsp =E1 + E5
  X.FnReqAny = E2
  X.FnRspAny = E3

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) +(E4->E5) + (E6->E7) in X.sb
  X.sthd = sq[E0+E1+E2+E3+E4+E5] + sq[E6+E7]
  sq[E0+E1+E4+E5+E6+E7] in X.sloc
  (E1->E5) in X.co
  X.rf = (E1->E7) + (E5->E6) 
  }
}

//Disallowed. The CPU can not see previous values
pred cpu_read_old_values[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.WrReq = E0 + E2
  X.WrRsp =E1 + E3
  X.CpuRead = E4 + E5


  (E0->E1) + (E1->E2) + (E2->E3) + (E4->E5) in X.sb
  X.sthd = sq[E0+E1+E2+E3] + sq[E4+E5]
  (E1->E3) in X.co
  sq[E0+E1+E2+E3+E4+E5] in X.sloc
  X.rf = (E1->E5) + (E3->E4) 
  }
}

//Disalllowed
pred fpga_sch_fence_cpu_read[X:Exec_F] {
  consistent[none->none, X]
  some disj E7, E6, E5, E4, E3, E2, E1, E0 : E {

  X.CpuRead = E6 + E7
  X.WrReq = E0 + E4
  X.WrRsp =E1 + E5
  X.FnReq = E2
  X.FnRsp = E3

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) +(E4->E5) + (E6->E7) in X.sb
  X.sthd = sq[E0+E1+E2+E3+E4+E5] + sq[E6+E7]
  sq[E0+E1+E2+E3+E4+E5] in X.sch 
  sq[E0+E1+E4+E5+E6+E7] in X.sloc
  X.rf = (E1->E7) + (E5->E6) 
  }
}



// Disallowed
pred propagation_page_1[X:Exec_F] {
  consistent[none->none, X]
  some disj E4, E3, E2, E1, E0 : E {

  X.CpuWrite = E0 + E1 + E2
  X.CpuFence = E3
  X.CpuRead = E4

  (E0->E1) + (E2->E3) + (E3->E4) in X.sb
  (E4->E0) in X.fr
  (E1->E2) in X.co
  X.sloc = sq[E0 + E4] + sq[E1+E2]
  }
}

// Disallowed
pred propagation_page_2[X:Exec_F] {
  consistent[none->none, X]
  some disj E6, E5, E4, E3, E2, E1, E0 : E {

  X.WrReq = E0 + E2
  X.WrRsp = E1 + E3
  X.CpuWrite = E4
  X.CpuFence = E5
  X.CpuRead = E6

  (E0->E1) + (E1->E2) + (E2->E3) + (E4->E5) + (E5->E6) in X.sb
  sq[E0+E1+E2+E3] in X.sch
  X.sloc = sq[E0+E1+E6] + sq[E2+E3+E4]
  (E6->E1) in X.fr
  (E3->E4) in X.co
  }
}

// Disallowed
pred propagation_page_3[X:Exec_F] {
  consistent[none->none, X]
  some disj E8, E7, E6, E5, E4, E3, E2, E1, E0 : E {

  X.WrReq = E0 + E4 
  X.FnReq = E1
  X.WrRsp = E2 + E5
  X.FnRsp = E3
  X.CpuWrite = E6
  X.CpuFence = E7
  X.CpuRead = E8

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) + (E4->E5) + (E6->E7) + (E7->E8) in X.sb
  X.sch = sq[E0+E1+E2+E3] + sq[E4+E5]
  X.sloc = sq[E0+E2+E8] + sq[E4+E5+E6]
  (E8->E2) in X.fr
  (E5->E6) in X.co
  }
}

// Disallowed
pred propagation_page_4[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.CpuWrite = E0 + E1
  X.WrReq = E2
  X.WrRsp = E3
  X.RdReq = E4
  X.RdRsp = E5

  (E0->E1) + (E2->E3) + (E3->E4) + (E4->E5) in X.sb
  sq[E2+E3+E4+E5] in X.sch
  X.sloc = sq[E0+E4+E5] + sq[E1+E2+E3]
  (E5->E0) in X.fr
  (E1->E3) in X.co
  }
}


// Disallowed
pred propagation_page_5[X:Exec_F] {
  consistent[none->none, X]
  some disj E7, E6, E5, E4, E3, E2, E1, E0 : E {

  X.CpuWrite = E0 + E1
  X.WrReq = E2
  X.WrRsp = E3
  X.FnReq = E4
  X.FnRsp = E5
  X.RdReq = E6
  X.RdRsp = E7

  (E0->E1) + (E2->E3) + (E3->E4) + (E4->E5) + (E5->E6) + (E6->E7) in X.sb
  sq[E2+E3+E4+E5]  + sq[E6+E7] in X.sch
  X.sloc = sq[E0+E6+E7] + sq[E1+E2+E3]
  (E7->E0) in X.fr
  (E1->E3) in X.co
  }
}

// Allowed
pred fence_on_reads[X:Exec_F] {
  consistent[none->none, X]
  some disj E6, E5, E4, E3, E2, E1, E0 : E {

  X.RdReq = E0 + E1
  X.RdRsp = E2 + E5
  X.FnReqAny = E3
  X.FnRspAny = E4
  X.CpuWrite = E6 

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) + (E4->E5) in X.sb
  sq[E0 + E2]  + sq[E1+E5] in X.sch
  X.sloc = sq[E0 + E1 + E2 + E5 + E6]
  (E0->E2) + (E1->E5) in X.readpair
  (E6->E2) in X.rf
  (E5->E6) in X.fr
  }
}

pred red_req_and_fence[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.WrReq = E0
  X.RdReq = E1
  X.FnReq = E2
  X.FnRsp = E4
  X.WrRsp = E3
  X.RdRsp = E5

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) + (E4->E5) in X.sb
  sq[E0 + E1 + E2 + E3 +E4 + E5] in X.sch
  X.sloc = sq[E0 + E1 + E3 + E5]
  (E5->E3) in X.fr
  }
}

pred red_req_and_fence2[X:Exec_F] {
  consistent[none->none, X]
  some disj E6, E5, E4, E3, E2, E1, E0 : E {

  X.WrReq = E0
  X.FnReqAny = E1
  X.WrRsp = E2
  X.RdReq = E3
  X.FnRspAny = E4
  X.RdRsp = E5
  X.CpuWrite = E6

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) + (E4->E5) in X.sb
  sq[E0 + E2] + sq[E3 + E5] in X.sch
  X.sloc = sq[E0 + E2 + E3 + E5 + E6]
  (E5->E2) + (E5->E6) in X.fr
  (E6->E2) in X.co
  }
}

pred red_req_and_fence3[X:Exec_F] {
  consistent[none->none, X]
  some disj E6, E5, E4, E3, E2, E1, E0 : E {

  X.RdReq = E0
  X.WrReq = E1
  X.WrRsp = E2
  X.FnReq = E3
  X.FnRsp = E4
  X.RdRsp = E5
  X.CpuWrite = E6

  (E0->E1) + (E1->E2) + (E2->E3) + (E3->E4) + (E4->E5) in X.sb
  sq[E0 + E5] + sq[E1+E2+E3 + E4] in X.sch
  X.sloc = sq[E0 + E1 + E2 + E5 + E6]
  (E5->E2) + (E5->E6) in X.fr
  (E6->E2) in X.co
  }
}

// Disallowed
pred wrreq_cpu_allowed[X:Exec_F] {
  consistent[none->none, X]
  some disj E5, E4, E3, E2, E1, E0 : E {

  X.WrReq = E0 + E1
  X.WrRsp = E2 + E3
  X.CpuRead = E4
  X.CpuWrite = E5

  (E0->E1) + (E1->E2) + (E2->E3) +  (E4->E5) in X.sb
  (E0->E2) + (E1->E3) in X.writepair
  sq[E0 + E1 + E2 + E3] in X.sch
  X.sloc = sq[E0 + E2 + E5] + sq[E1 + E3 + E4]
  X.rf = (E3->E4)
  X.co = (E5->E2)
  }
}

run wrreq_cpu_allowed for 1 Exec_F, exactly 6 E expect 0
run red_req_and_fence3 for 1 Exec_F, exactly 7 E expect 1
run red_req_and_fence2 for 1 Exec_F, exactly 7 E expect 1
run red_req_and_fence for 1 Exec_F, exactly 6 E expect 1
run cpu_read_old_values for 1 Exec_F, exactly 6 E expect 0
run fpga_fence_cpu_read for 1 Exec_F, exactly 8 E expect 0
run fpga_sch_fence_cpu_read	 for 1 Exec_F, exactly 8 E expect 0
run fence_on_reads for 1 Exec_F, exactly 7 E expect 1

run store_buffering for 1 Exec_F, exactly 4 E expect 1

run page1_ex1 for 1 Exec_F, exactly 4 E expect 1  
run page1_ex2 for 1 Exec_F, exactly 4 E expect 0
run page1_ex3 for 1 Exec_F, exactly 6 E expect 1
run page1_ex4 for 1 Exec_F, exactly 6 E expect 1
run page1_ex5 for 1 Exec_F, exactly 6 E expect 0
run page1_ex6 for 1 Exec_F, exactly 6 E expect 0
run page1_ex7 for 1 Exec_F, exactly 6 E expect 1
run page1_ex8 for 1 Exec_F, exactly 6 E expect 1
run page1_ex9 for 1 Exec_F, exactly 6 E expect 1
run page1_ex10 for 1 Exec_F, exactly 6 E expect 0
run page1_ex11 for 1 Exec_F, exactly 6 E expect 0


run page2_ex1 for 1 Exec_F, exactly 4 E expect 0
run page2_ex2 for 1 Exec_F, exactly 4 E expect 0
run page2_ex3 for 1 Exec_F, exactly 6 E expect 0
run page2_ex4 for 1 Exec_F, exactly 6 E expect 0
run page2_ex5 for 1 Exec_F, exactly 6 E expect 0



run example1 for 1 Exec_F, exactly 4 E expect 1
run example2 for 1 Exec_F, exactly 4 E expect 1
run example3_single for 1 Exec_F, exactly 6 E expect 0
run example3_any for 1 Exec_F, exactly 6 E expect 0
run example4 for 1 Exec_F, exactly 8 E expect 1
run example5 for 1 Exec_F, exactly 8 E expect 1
run example6 for 1 Exec_F, exactly 8 E expect 0
//run example7 for 1 Exec_F, exactly 10 E expect 0
run example8 for 1 Exec_F, exactly 6 E expect 1
run example9 for 1 Exec_F, exactly 6 E expect 0
run example10 for 1 Exec_F, exactly 4 E expect 1

run fence_order_test for 1 Exec_F, exactly 6 E expect 0

run cpu_fpga1 for 1 Exec_F, exactly 6 E expect 1
run cpu_fpga2 for 1 Exec_F, exactly 6 E expect 0
run cpu_fpga3 for 1 Exec_F, exactly 6 E expect 1
run cpu_fpga4 for 1 Exec_F, exactly 6 E expect 1
run cpu_fpga6 for 1 Exec_F, exactly 6 E expect 1
run cpu_fpga7 for 1 Exec_F, exactly 6 E expect 0

run automatic_trace1 for 1 Exec_F, exactly 4 E expect 0
run automatic_trace2 for 1 Exec_F, exactly 4 E expect 0



run propagation_page_1 for  1 Exec_F, exactly 5 E expect 0
run propagation_page_2 for  1 Exec_F, exactly 7 E expect 0
run propagation_page_3 for  1 Exec_F, exactly 9 E expect 0
run propagation_page_4 for  1 Exec_F, exactly 6 E expect 0
run propagation_page_5 for  1 Exec_F, exactly 8 E expect 0




