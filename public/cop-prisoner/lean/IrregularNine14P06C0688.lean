import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0508
import IrregularNine14P06C0509
import IrregularNine14P06C0510
import IrregularNine14P06C0511
import IrregularNine14P06C0512

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41280 : PairBound 9 := { available := 469, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 44 469 501 469 469 469), lower := (rows 11 35 70 44 16 32 64 128 256), losses := [] }

theorem u41280 : Upper (D 6) (R 6) [10,33,66,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41281 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 56 469 485 453 453 453), lower := (rows 11 35 70 56 16 32 64 128 256), losses := [] }

theorem u41281 : Upper (D 6) (R 6) [10,33,66,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41282 : PairBound 9 := { available := 436, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 2, region := 9, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 70 73 436 436 500 436 436), lower := (rows 11 35 70 73 16 32 64 128 256), losses := [] }

theorem u41282 : Upper (D 6) (R 6) [10,33,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41283 : PairBound 9 := { available := 437, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 35 70 76 437 437 501 437 437), lower := (rows 11 35 70 76 16 32 64 128 256), losses := [] }

theorem u41283 : Upper (D 6) (R 6) [10,33,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41284 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41284 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41284 : Upper (D 6) (R 6) [10,33,66,80] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80] 13 (by decide) (choices 2) [5,33,36,129,132,160,384] r41284 c41284
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30533
  · exact u30534
  · exact u30535
  · exact u30536
  · exact u30537
  · exact u30538
  · exact u30539

def b41285 : PairBound 9 := { available := 405, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 104 405 437 469 405 405), lower := (rows 11 35 70 104 16 32 64 128 256), losses := [] }

theorem u41285 : Upper (D 6) (R 6) [10,33,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41286 : PairBound 9 := { available := 372, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 304, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 35 70 137 372 372 372 500 372), lower := (rows 11 35 70 137 16 32 64 128 256), losses := [] }

theorem u41286 : Upper (D 6) (R 6) [10,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41287 : Route 9 := (fun mask => (mask,id))

def c41287 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41287 : Upper (D 6) (R 6) [10,33,66,132] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41287 c41287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30540
  · exact u30541
  · exact u30542
  · exact u30543
  · exact u30544
  · exact u30545
  · exact u30546
  · exact u30547
  · exact u30548
  · exact u30549

def r41288 : Route 9 := (fun mask => (mask,id))

def c41288 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41288 : Upper (D 6) (R 6) [10,33,66,144] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41288 c41288
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30550
  · exact u30551
  · exact u30552
  · exact u30553
  · exact u30554
  · exact u30555
  · exact u30556
  · exact u30557
  · exact u30558
  · exact u30559

def b41289 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 168 341 373 341 469 341), lower := (rows 11 35 70 168 16 32 64 128 256), losses := [] }

theorem u41289 : Upper (D 6) (R 6) [10,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41290 : Route 9 := (fun mask => (mask,id))

def c41290 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41290 : Upper (D 6) (R 6) [10,33,66,192] 13 := by
  apply FastRouting.sound _ _ [10,33,66,192] 13 (by decide) (choices 2) [5,33,36,257,260,288] r41290 c41290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30560
  · exact u30561
  · exact u30562
  · exact u30563
  · exact u30564
  · exact u30565

def r41291 : Route 9 := (fun mask => (mask,id))

def c41291 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41291 : Upper (D 6) (R 6) [10,33,66,384] 13 := by
  apply FastRouting.sound _ _ [10,33,66,384] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41291 c41291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30566
  · exact u30567
  · exact u30568
  · exact u30569
  · exact u30570
  · exact u30571

def b41292 : PairBound 9 := { available := 484, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 84 11 500 484 484 484 484), lower := (rows 11 35 84 11 16 32 64 128 256), losses := [] }

theorem u41292 : Upper (D 6) (R 6) [10,33,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41293 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41293 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41293 : Upper (D 6) (R 6) [10,33,80,5] 13 := by
  apply FastRouting.sound _ _ [10,33,80,5] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r41293 c41293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30572
  · exact u30573
  · exact u30574
  · exact u30575
  · exact u30576
  · exact u30577
  · exact u30578
  · exact u30579
  · exact u30580
  · exact u30581
  · exact u30582

def b41294 : PairBound 9 := { available := 485, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 84 14 501 485 485 485 485), lower := (rows 11 35 84 14 16 32 64 128 256), losses := [] }

theorem u41294 : Upper (D 6) (R 6) [10,33,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41295 : PairBound 9 := { available := 454, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 41 470 486 454 454 454), lower := (rows 11 35 84 41 16 32 64 128 256), losses := [] }

theorem u41295 : Upper (D 6) (R 6) [10,33,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41296 : PairBound 9 := { available := 453, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 42 469 485 453 453 453), lower := (rows 11 35 84 42 16 32 64 128 256), losses := [] }

theorem u41296 : Upper (D 6) (R 6) [10,33,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41297 : PairBound 9 := { available := 455, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 44 471 487 455 455 455), lower := (rows 11 35 84 44 16 32 64 128 256), losses := [] }

theorem u41297 : Upper (D 6) (R 6) [10,33,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41298 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41298 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41298 : Upper (D 6) (R 6) [10,33,80,65] 13 := by
  apply FastRouting.sound _ _ [10,33,80,65] 13 (by decide) (choices 2) [6,34,36,130,132,160,384] r41298 c41298
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30583
  · exact u30584
  · exact u30585
  · exact u30586
  · exact u30587
  · exact u30588
  · exact u30589

def b41299 : PairBound 9 := { available := 421, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 84 74 437 421 485 421 421), lower := (rows 11 35 84 74 16 32 64 128 256), losses := [] }

theorem u41299 : Upper (D 6) (R 6) [10,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41300 : PairBound 9 := { available := 423, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 84 76 439 423 487 423 423), lower := (rows 11 35 84 76 16 32 64 128 256), losses := [] }

theorem u41300 : Upper (D 6) (R 6) [10,33,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41301 : PairBound 9 := { available := 391, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 104 407 423 455 391 391), lower := (rows 11 35 84 104 16 32 64 128 256), losses := [] }

theorem u41301 : Upper (D 6) (R 6) [10,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41302 : Route 9 := (fun mask => (mask,id))

def c41302 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41302 : Upper (D 6) (R 6) [10,33,80,129] 13 := by
  apply FastRouting.sound _ _ [10,33,80,129] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41302 c41302
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30590
  · exact u30591
  · exact u30592
  · exact u30593
  · exact u30594
  · exact u30595
  · exact u30596
  · exact u30597
  · exact u30598
  · exact u30599

def b41303 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 84 138 373 357 357 485 357), lower := (rows 11 35 84 138 16 32 64 128 256), losses := [] }

theorem u41303 : Upper (D 6) (R 6) [10,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41304 : Route 9 := (fun mask => (mask,id))

def c41304 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41304 : Upper (D 6) (R 6) [10,33,80,132] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41304 c41304
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30600
  · exact u30601
  · exact u30602
  · exact u30603
  · exact u30604
  · exact u30605
  · exact u30606
  · exact u30607
  · exact u30608
  · exact u30609
  · exact u30610
  · exact u30611
  · exact u30612
  · exact u30613
  · exact u30614

def b41305 : PairBound 9 := { available := 327, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 168 343 359 327 455 327), lower := (rows 11 35 84 168 16 32 64 128 256), losses := [] }

theorem u41305 : Upper (D 6) (R 6) [10,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41306 : Route 9 := (fun mask => (mask,id))

def c41306 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41306 : Upper (D 6) (R 6) [10,33,80,192] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r41306 c41306
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30615
  · exact u30616
  · exact u30617
  · exact u30618
  · exact u30619
  · exact u30620
  · exact u30621
  · exact u30622
  · exact u30623
  · exact u30624

def r41307 : Route 9 := (fun mask => (mask,id))

def c41307 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41307 : Upper (D 6) (R 6) [10,33,80,384] 13 := by
  apply FastRouting.sound _ _ [10,33,80,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41307 c41307
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30625
  · exact u30626
  · exact u30627
  · exact u30628
  · exact u30629
  · exact u30630
  · exact u30631
  · exact u30632
  · exact u30633
  · exact u30634

def b41308 : PairBound 9 := { available := 468, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 100 11 468 500 468 468 468), lower := (rows 11 35 100 11 16 32 64 128 256), losses := [] }

theorem u41308 : Upper (D 6) (R 6) [10,33,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41309 : PairBound 9 := { available := 470, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 13 470 502 470 470 470), lower := (rows 11 35 100 13 16 32 64 128 256), losses := [] }

theorem u41309 : Upper (D 6) (R 6) [10,33,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41310 : PairBound 9 := { available := 469, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 100 14 469 501 469 469 469), lower := (rows 11 35 100 14 16 32 64 128 256), losses := [] }

theorem u41310 : Upper (D 6) (R 6) [10,33,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41311 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41311 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41311 : Upper (D 6) (R 6) [10,33,96,17] 13 := by
  apply FastRouting.sound _ _ [10,33,96,17] 13 (by decide) (choices 2) [6,66,68,130,132,192,384] r41311 c41311
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30635
  · exact u30636
  · exact u30637
  · exact u30638
  · exact u30639
  · exact u30640
  · exact u30641

def b41312 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 100 26 469 485 453 453 453), lower := (rows 11 35 100 26 16 32 64 128 256), losses := [] }

theorem u41312 : Upper (D 6) (R 6) [10,33,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41313 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41313 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41313 : Upper (D 6) (R 6) [10,33,96,20] 13 := by
  apply FastRouting.sound _ _ [10,33,96,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41313 c41313
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30642
  · exact u30643
  · exact u30644
  · exact u30645
  · exact u30646
  · exact u30647
  · exact u30648
  · exact u30649
  · exact u30650
  · exact u30651
  · exact u30652

def b41314 : PairBound 9 := { available := 406, camps := [{ cop := 2, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 100 73 406 438 470 406 406), lower := (rows 11 35 100 73 16 32 64 128 256), losses := [] }

theorem u41314 : Upper (D 6) (R 6) [10,33,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41315 : PairBound 9 := { available := 405, camps := [{ cop := 2, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 100 74 405 437 469 405 405), lower := (rows 11 35 100 74 16 32 64 128 256), losses := [] }

theorem u41315 : Upper (D 6) (R 6) [10,33,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41316 : PairBound 9 := { available := 407, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 100 76 407 439 471 407 407), lower := (rows 11 35 100 76 16 32 64 128 256), losses := [] }

theorem u41316 : Upper (D 6) (R 6) [10,33,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41317 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41317 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41317 : Upper (D 6) (R 6) [10,33,96,80] 13 := by
  apply FastRouting.sound _ _ [10,33,96,80] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r41317 c41317
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30653
  · exact u30654
  · exact u30655
  · exact u30656
  · exact u30657
  · exact u30658
  · exact u30659

def r41318 : Route 9 := (fun mask => (mask,id))

def c41318 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41318 : Upper (D 6) (R 6) [10,33,96,129] 13 := by
  apply FastRouting.sound _ _ [10,33,96,129] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41318 c41318
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30660
  · exact u30661
  · exact u30662
  · exact u30663
  · exact u30664
  · exact u30665

def b41319 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 100 138 341 373 341 469 341), lower := (rows 11 35 100 138 16 32 64 128 256), losses := [] }

theorem u41319 : Upper (D 6) (R 6) [10,33,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41320 : Route 9 := (fun mask => (mask,id))

def c41320 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41320 : Upper (D 6) (R 6) [10,33,96,132] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41320 c41320
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30666
  · exact u30667
  · exact u30668
  · exact u30669
  · exact u30670
  · exact u30671
  · exact u30672
  · exact u30673
  · exact u30674
  · exact u30675

def r41321 : Route 9 := (fun mask => (mask,id))

def c41321 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41321 : Upper (D 6) (R 6) [10,33,96,144] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41321 c41321
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30676
  · exact u30677
  · exact u30678
  · exact u30679
  · exact u30680
  · exact u30681
  · exact u30682
  · exact u30683
  · exact u30684
  · exact u30685

def r41322 : Route 9 := (fun mask => (mask,id))

def c41322 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41322 : Upper (D 6) (R 6) [10,33,96,192] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192] 13 (by decide) (choices 2) [3,5,6,257,258,260] r41322 c41322
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30686
  · exact u30687
  · exact u30688
  · exact u30689
  · exact u30690
  · exact u30691

def r41323 : Route 9 := (fun mask => (mask,id))

def c41323 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41323 : Upper (D 6) (R 6) [10,33,96,384] 13 := by
  apply FastRouting.sound _ _ [10,33,96,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41323 c41323
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30692
  · exact u30693
  · exact u30694
  · exact u30695
  · exact u30696
  · exact u30697

def b41324 : PairBound 9 := { available := 372, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 133 14 372 372 372 500 372), lower := (rows 11 35 133 14 16 32 64 128 256), losses := [] }

theorem u41324 : Upper (D 6) (R 6) [10,33,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41325 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 133 26 372 356 356 484 356), lower := (rows 11 35 133 26 16 32 64 128 256), losses := [] }

theorem u41325 : Upper (D 6) (R 6) [10,33,129,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41326 : Route 9 := (fun mask => (mask,id))

def c41326 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41326 : Upper (D 6) (R 6) [10,33,129,20] 13 := by
  apply FastRouting.sound _ _ [10,33,129,20] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41326 c41326
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30698
  · exact u30699
  · exact u30700
  · exact u30701
  · exact u30702
  · exact u30703
  · exact u30704
  · exact u30705
  · exact u30706
  · exact u30707

def b41327 : PairBound 9 := { available := 340, camps := [{ cop := 5, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 42 340 372 340 468 340), lower := (rows 11 35 133 42 16 32 64 128 256), losses := [] }

theorem u41327 : Upper (D 6) (R 6) [10,33,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41328 : PairBound 9 := { available := 342, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 44 342 374 342 470 342), lower := (rows 11 35 133 44 16 32 64 128 256), losses := [] }

theorem u41328 : Upper (D 6) (R 6) [10,33,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41329 : PairBound 9 := { available := 326, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 56 342 358 326 454 326), lower := (rows 11 35 133 56 16 32 64 128 256), losses := [] }

theorem u41329 : Upper (D 6) (R 6) [10,33,129,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41330 : PairBound 9 := { available := 372, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 133 74 372 372 372 500 372), lower := (rows 11 35 133 74 16 32 64 128 256), losses := [] }

theorem u41330 : Upper (D 6) (R 6) [10,33,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41331 : Route 9 := (fun mask => (mask,id))

def c41331 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41331 : Upper (D 6) (R 6) [10,33,129,68] 13 := by
  apply FastRouting.sound _ _ [10,33,129,68] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41331 c41331
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30708
  · exact u30709
  · exact u30710
  · exact u30711
  · exact u30712
  · exact u30713
  · exact u30714
  · exact u30715
  · exact u30716
  · exact u30717

def r41332 : Route 9 := (fun mask => (mask,id))

def c41332 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41332 : Upper (D 6) (R 6) [10,33,129,80] 13 := by
  apply FastRouting.sound _ _ [10,33,129,80] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41332 c41332
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30718
  · exact u30719
  · exact u30720
  · exact u30721
  · exact u30722
  · exact u30723
  · exact u30724
  · exact u30725
  · exact u30726
  · exact u30727

def b41333 : PairBound 9 := { available := 342, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 104 342 374 342 470 342), lower := (rows 11 35 133 104 16 32 64 128 256), losses := [] }

theorem u41333 : Upper (D 6) (R 6) [10,33,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41334 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 133 266 116 116 116 244 372), lower := (rows 11 35 133 266 16 32 64 128 256), losses := [] }

theorem u41334 : Upper (D 6) (R 6) [10,33,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41335 : Route 9 := (fun mask => (mask,id))

def c41335 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41335 : Upper (D 6) (R 6) [10,33,129,260] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41335 c41335
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30728
  · exact u30729
  · exact u30730
  · exact u30731
  · exact u30732
  · exact u30733

def r41336 : Route 9 := (fun mask => (mask,id))

def c41336 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41336 : Upper (D 6) (R 6) [10,33,129,272] 13 := by
  apply FastRouting.sound _ _ [10,33,129,272] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41336 c41336
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30734
  · exact u30735
  · exact u30736
  · exact u30737
  · exact u30738
  · exact u30739

def b41337 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 133 296 86 118 86 214 342), lower := (rows 11 35 133 296 16 32 64 128 256), losses := [] }

theorem u41337 : Upper (D 6) (R 6) [10,33,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41338 : Route 9 := (fun mask => (mask,id))

def c41338 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41338 : Upper (D 6) (R 6) [10,33,129,320] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41338 c41338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30740
  · exact u30741
  · exact u30742
  · exact u30743
  · exact u30744
  · exact u30745

def b41339 : PairBound 9 := { available := 372, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 134 13 372 372 372 500 372), lower := (rows 11 35 134 13 16 32 64 128 256), losses := [] }

theorem u41339 : Upper (D 6) (R 6) [10,33,130,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u41339
end Delivery.IrregularNine14.P06
