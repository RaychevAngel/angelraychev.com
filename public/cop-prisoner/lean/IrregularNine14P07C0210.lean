import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0022
import IrregularNine14P07C0023

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12600 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 0, region := 240, targets := 1 }], pairs := [(0,6),(2,0),(2,1),(4,0)], upper := (rows 7 35 268 25 82 96 224 160 416), lower := (rows 7 35 268 25 82 96 64 128 256), losses := [{ target := 6, region := (rows 17 2 20 24 16 32 0 162 290), good := (rows 391 419 268 29 415 416 0 128 256) }] }

theorem u12600 : Upper (D 7) (R 7) [6,33,264,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12601 : Route 9 := (fun mask => (mask,id))

def c12601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12601 : Upper (D 7) (R 7) [6,33,264,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,17,66,128] 13 (by decide) (choices 1) [32,128] r12601 c12601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1350
  · exact u1351

def b12602 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 25 112 34 192 192 448), lower := (rows 7 35 268 25 112 34 64 128 256), losses := [] }

theorem u12602 : Upper (D 7) (R 7) [6,33,264,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12603 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 35 268 25 112 96 194 130 386), lower := (rows 7 35 268 25 112 96 64 128 256), losses := [] }

theorem u12603 : Upper (D 7) (R 7) [6,33,264,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12604 : Route 9 := (fun mask => (mask,id))

def c12604 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12604 : Upper (D 7) (R 7) [6,33,264,17,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,17,96,128] 13 (by decide) (choices 1) [2,128] r12604 c12604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1352
  · exact u1353

def b12605 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 25 208 34 224 224 480), lower := (rows 7 35 268 25 208 34 64 128 256), losses := [] }

theorem u12605 : Upper (D 7) (R 7) [6,33,264,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12606 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 7 35 268 25 208 96 226 162 418), lower := (rows 7 35 268 25 208 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 123 67 131 259), good := (rows 502 498 316 508 240 96 96 128 256) },{ target := 7, region := (rows 5 10 4 8 16 112 64 0 256), good := (rows 7 35 271 59 112 96 96 0 256) }] }

theorem u12606 : Upper (D 7) (R 7) [6,33,264,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12607 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 4, region := 42, targets := 128 }], pairs := [(1,7),(2,0),(2,1),(3,7)], upper := (rows 7 35 268 26 81 96 224 160 416), lower := (rows 7 35 268 26 81 96 64 128 256), losses := [] }

theorem u12607 : Upper (D 7) (R 7) [6,33,264,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12608 : Route 9 := (fun mask => (mask,id))

def c12608 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12608 : Upper (D 7) (R 7) [6,33,264,18,65,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,18,65,128] 13 (by decide) (choices 1) [32,128] r12608 c12608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1354
  · exact u1355

def b12609 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 26 208 33 224 224 480), lower := (rows 7 35 268 26 208 33 64 128 256), losses := [] }

theorem u12609 : Upper (D 7) (R 7) [6,33,264,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12610 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 240, targets := 2 }], pairs := [(0,6),(2,1),(2,6),(4,1)], upper := (rows 7 35 268 26 208 96 225 161 417), lower := (rows 7 35 268 26 208 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 123 67 131 259), good := (rows 501 497 316 508 240 96 96 128 256) },{ target := 6, region := (rows 9 2 12 8 16 32 0 130 258), good := (rows 391 419 269 415 144 32 0 128 256) }] }

theorem u12610 : Upper (D 7) (R 7) [6,33,264,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12611 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 56 81 34 192 192 448), lower := (rows 7 35 268 56 81 34 64 128 256), losses := [] }

theorem u12611 : Upper (D 7) (R 7) [6,33,264,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12612 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 268 56 81 96 194 130 386), lower := (rows 7 35 268 56 81 96 64 128 256), losses := [] }

theorem u12612 : Upper (D 7) (R 7) [6,33,264,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12613 : Route 9 := (fun mask => (mask,id))

def c12613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12613 : Upper (D 7) (R 7) [6,33,264,48,65,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,48,65,128] 13 (by decide) (choices 1) [2,128] r12613 c12613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1356
  · exact u1357

def b12614 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 56 82 33 192 192 448), lower := (rows 7 35 268 56 82 33 64 128 256), losses := [] }

theorem u12614 : Upper (D 7) (R 7) [6,33,264,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12615 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 268 56 82 96 193 129 385), lower := (rows 7 35 268 56 82 96 64 128 256), losses := [] }

theorem u12615 : Upper (D 7) (R 7) [6,33,264,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12616 : Route 9 := (fun mask => (mask,id))

def c12616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12616 : Upper (D 7) (R 7) [6,33,264,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,48,66,128] 13 (by decide) (choices 1) [1,128] r12616 c12616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1358
  · exact u1359

def b12617 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 56 208 33 194 194 450), lower := (rows 7 35 268 56 208 33 64 128 256), losses := [] }

theorem u12617 : Upper (D 7) (R 7) [6,33,264,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12618 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 56 208 34 193 193 449), lower := (rows 7 35 268 56 208 34 64 128 256), losses := [] }

theorem u12618 : Upper (D 7) (R 7) [6,33,264,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12619 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 35 268 56 208 96 195 131 387), lower := (rows 7 35 268 56 208 96 64 128 256), losses := [] }

theorem u12619 : Upper (D 7) (R 7) [6,33,264,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12620 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 460, targets := 2 },{ cop := 3, region := 50, targets := 128 }], pairs := [(1,7),(2,1),(3,1)], upper := (rows 7 35 268 73 82 48 224 160 416), lower := (rows 7 35 268 73 82 48 64 128 256), losses := [] }

theorem u12620 : Upper (D 7) (R 7) [6,33,264,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12620 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12621 : Route 9 := (fun mask => (mask,id))

def c12621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12621 : Upper (D 7) (R 7) [6,33,264,65,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,66,128] 13 (by decide) (choices 1) [16,32,128] r12621 c12621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1360
  · exact u1361
  · exact u1362

def b12622 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 73 112 34 208 144 400), lower := (rows 7 35 268 73 112 34 64 128 256), losses := [] }

theorem u12622 : Upper (D 7) (R 7) [6,33,264,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12623 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 268 73 112 48 194 130 386), lower := (rows 7 35 268 73 112 48 64 128 256), losses := [] }

theorem u12623 : Upper (D 7) (R 7) [6,33,264,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12623 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12624 : Route 9 := (fun mask => (mask,id))

def c12624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12624 : Upper (D 7) (R 7) [6,33,264,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,96,128] 13 (by decide) (choices 1) [2,16,128] r12624 c12624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1363
  · exact u1364
  · exact u1365

def b12625 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 460, targets := 2 },{ cop := 0, region := 240, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 35 268 73 146 48 224 224 480), lower := (rows 7 35 268 73 146 48 64 128 256), losses := [] }

theorem u12625 : Upper (D 7) (R 7) [6,33,264,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12625 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12626 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 240, targets := 1 },{ cop := 1, region := 144, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(2,0),(4,0),(4,6)], upper := (rows 7 35 268 73 146 96 240 176 432), lower := (rows 7 35 268 73 146 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 127 91 155 283), good := (rows 502 498 492 508 498 96 96 128 256) }] }

theorem u12626 : Upper (D 7) (R 7) [6,33,264,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12627 : Route 9 := (fun mask => (mask,id))

def c12627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12627 : Upper (D 7) (R 7) [6,33,264,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,130,128] 13 (by decide) (choices 1) [16,32] r12627 c12627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1366
  · exact u1367

def b12628 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 73 176 34 208 208 464), lower := (rows 7 35 268 73 176 34 64 128 256), losses := [] }

theorem u12628 : Upper (D 7) (R 7) [6,33,264,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12629 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 268 73 176 48 194 194 450), lower := (rows 7 35 268 73 176 48 64 128 256), losses := [] }

theorem u12629 : Upper (D 7) (R 7) [6,33,264,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12629 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12630 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 240, targets := 1 },{ cop := 1, region := 144, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(2,0),(4,0),(4,6)], upper := (rows 7 35 268 73 176 96 210 146 402), lower := (rows 7 35 268 73 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 107 67 131 259), good := (rows 502 498 316 508 176 96 96 128 256) }] }

theorem u12630 : Upper (D 7) (R 7) [6,33,264,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12631 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 268 73 176 160 82 210 338), lower := (rows 7 35 268 73 176 160 64 128 256), losses := [] }

theorem u12631 : Upper (D 7) (R 7) [6,33,264,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12632 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 73 208 34 240 176 432), lower := (rows 7 35 268 73 208 34 64 128 256), losses := [] }

theorem u12632 : Upper (D 7) (R 7) [6,33,264,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12633 : Route 9 := (fun mask => (mask,id))

def c12633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12633 : Upper (D 7) (R 7) [6,33,264,65,192,16] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,192,16] 13 (by decide) (choices 1) [2,32,128] r12633 c12633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1368
  · exact u1369
  · exact u1370

def r12634 : Route 9 := (fun mask => (mask,id))

def c12634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12634 : Upper (D 7) (R 7) [6,33,264,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,192,128] 13 (by decide) (choices 1) [2,16,32] r12634 c12634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1371
  · exact u1372
  · exact u1373

def b12635 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,7),(2,0),(3,0)], upper := (rows 7 35 268 74 81 48 224 160 416), lower := (rows 7 35 268 74 81 48 64 128 256), losses := [] }

theorem u12635 : Upper (D 7) (R 7) [6,33,264,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12635 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12636 : Route 9 := (fun mask => (mask,id))

def c12636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12636 : Upper (D 7) (R 7) [6,33,264,66,65,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66,65,128] 13 (by decide) (choices 1) [16,32,128] r12636 c12636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1374
  · exact u1375
  · exact u1376

def b12637 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 74 112 33 208 144 400), lower := (rows 7 35 268 74 112 33 64 128 256), losses := [] }

theorem u12637 : Upper (D 7) (R 7) [6,33,264,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12638 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 268 74 112 48 193 129 385), lower := (rows 7 35 268 74 112 48 64 128 256), losses := [] }

theorem u12638 : Upper (D 7) (R 7) [6,33,264,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12638 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12639 : Route 9 := (fun mask => (mask,id))

def c12639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12639 : Upper (D 7) (R 7) [6,33,264,66,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66,96,128] 13 (by decide) (choices 1) [1,16,128] r12639 c12639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1377
  · exact u1378
  · exact u1379

def b12640 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 268 74 145 48 224 224 480), lower := (rows 7 35 268 74 145 48 64 128 256), losses := [] }

theorem u12640 : Upper (D 7) (R 7) [6,33,264,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12640 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12641 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 144, targets := 64 }], pairs := [(0,6),(2,1),(4,1),(4,6)], upper := (rows 7 35 268 74 145 96 240 176 432), lower := (rows 7 35 268 74 145 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 127 91 155 283), good := (rows 501 497 492 508 497 96 96 128 256) },{ target := 6, region := (rows 9 2 12 8 27 32 0 130 258), good := (rows 407 435 285 415 145 32 0 128 256) }] }

theorem u12641 : Upper (D 7) (R 7) [6,33,264,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12642 : Route 9 := (fun mask => (mask,id))

def c12642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12642 : Upper (D 7) (R 7) [6,33,264,66,129,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66,129,128] 13 (by decide) (choices 1) [16,32] r12642 c12642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1380
  · exact u1381

def b12643 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 74 176 33 208 208 464), lower := (rows 7 35 268 74 176 33 64 128 256), losses := [] }

theorem u12643 : Upper (D 7) (R 7) [6,33,264,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12644 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 268 74 176 48 193 193 449), lower := (rows 7 35 268 74 176 48 64 128 256), losses := [] }

theorem u12644 : Upper (D 7) (R 7) [6,33,264,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12644 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12645 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 144, targets := 64 }], pairs := [(0,6),(2,1),(4,1),(4,6)], upper := (rows 7 35 268 74 176 96 209 145 401), lower := (rows 7 35 268 74 176 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 107 67 131 259), good := (rows 501 497 316 508 176 96 96 128 256) },{ target := 6, region := (rows 9 2 12 8 18 32 0 139 267), good := (rows 407 435 397 415 176 32 0 128 256) }] }

theorem u12645 : Upper (D 7) (R 7) [6,33,264,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12646 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 268 74 176 160 81 209 337), lower := (rows 7 35 268 74 176 160 64 128 256), losses := [] }

theorem u12646 : Upper (D 7) (R 7) [6,33,264,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12647 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 74 208 33 240 176 432), lower := (rows 7 35 268 74 208 33 64 128 256), losses := [] }

theorem u12647 : Upper (D 7) (R 7) [6,33,264,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12648 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 240, targets := 2 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 7 35 268 74 208 48 225 161 417), lower := (rows 7 35 268 74 208 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 63 67 131 259), good := (rows 501 497 316 508 240 48 64 128 256) },{ target := 6, region := (rows 9 2 12 8 16 48 0 130 258), good := (rows 391 419 269 399 176 48 0 128 256) }] }

theorem u12648 : Upper (D 7) (R 7) [6,33,264,66,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12648 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12649 : Route 9 := (fun mask => (mask,id))

def c12649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12649 : Upper (D 7) (R 7) [6,33,264,66,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66,192,128] 13 (by decide) (choices 1) [1,16,32] r12649 c12649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1382
  · exact u1383
  · exact u1384

def b12650 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 88 145 34 224 224 480), lower := (rows 7 35 268 88 145 34 64 128 256), losses := [] }

theorem u12650 : Upper (D 7) (R 7) [6,33,264,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12651 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 144, targets := 64 }], pairs := [(0,7),(2,0),(3,0),(4,6)], upper := (rows 7 35 268 88 145 96 226 162 418), lower := (rows 7 35 268 88 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 123 67 131 259), good := (rows 486 482 300 124 508 96 96 128 256) },{ target := 7, region := (rows 5 6 4 8 16 104 64 0 256), good := (rows 7 35 303 120 17 96 96 0 256) }] }

theorem u12651 : Upper (D 7) (R 7) [6,33,264,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12652 : Route 9 := (fun mask => (mask,id))

def c12652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12652 : Upper (D 7) (R 7) [6,33,264,80,129,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80,129,128] 13 (by decide) (choices 1) [2,32] r12652 c12652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1385
  · exact u1386

def b12653 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 88 146 33 224 224 480), lower := (rows 7 35 268 88 146 33 64 128 256), losses := [] }

theorem u12653 : Upper (D 7) (R 7) [6,33,264,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12654 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 144, targets := 64 }], pairs := [(0,7),(2,1),(3,1),(4,6)], upper := (rows 7 35 268 88 146 96 225 161 417), lower := (rows 7 35 268 88 146 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 123 67 131 259), good := (rows 485 481 300 124 508 96 96 128 256) },{ target := 7, region := (rows 5 6 4 8 16 104 64 0 256), good := (rows 7 35 303 120 18 96 96 0 256) }] }

theorem u12654 : Upper (D 7) (R 7) [6,33,264,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12655 : PairBound 9 := { available := 97, camps := [], pairs := [(0,7),(2,1),(2,7),(3,1)], upper := (rows 7 35 268 88 146 160 97 225 353), lower := (rows 7 35 268 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 179 67 131 259), good := (rows 485 481 268 124 508 160 64 160 256) },{ target := 7, region := (rows 17 2 20 24 16 32 66 0 258), good := (rows 327 355 268 93 351 32 64 0 256) }] }

theorem u12655 : Upper (D 7) (R 7) [6,33,264,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12656 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 88 176 33 194 194 450), lower := (rows 7 35 268 88 176 33 64 128 256), losses := [] }

theorem u12656 : Upper (D 7) (R 7) [6,33,264,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12657 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 88 176 34 193 193 449), lower := (rows 7 35 268 88 176 34 64 128 256), losses := [] }

theorem u12657 : Upper (D 7) (R 7) [6,33,264,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12658 : Route 9 := (fun mask => (mask,id))

def c12658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12658 : Upper (D 7) (R 7) [6,33,264,80,160,64] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80,160,64] 13 (by decide) (choices 1) [1,2,128] r12658 c12658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1387
  · exact u1388
  · exact u1389

def b12659 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 268 88 176 160 67 195 323), lower := (rows 7 35 268 88 176 160 64 128 256), losses := [] }

theorem u12659 : Upper (D 7) (R 7) [6,33,264,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12659
end Delivery.IrregularNine14.P07
