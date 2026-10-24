import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0041
import IrregularNine14P07C0042

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14520 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 292 88 145 40 195 131 387), lower := (rows 7 98 292 88 145 40 64 128 256), losses := [] }

theorem u14520 : Upper (D 7) (R 7) [6,96,288,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14520 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14521 : Route 9 := (fun mask => (mask,id))

def c14521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14521 : Upper (D 7) (R 7) [6,96,288,80,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80,129,128] 13 (by decide) (choices 1) [1,2,8] r14521 c14521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2504
  · exact u2505
  · exact u2506

def r14522 : Route 9 := (fun mask => (mask,id))

def c14522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14522 : Upper (D 7) (R 7) [6,96,288,80,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80,130,1] 13 (by decide) (choices 1) [1,8,128] r14522 c14522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2507
  · exact u2508
  · exact u2509

def b14523 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 292 88 146 40 193 129 385), lower := (rows 7 98 292 88 146 40 64 128 256), losses := [] }

theorem u14523 : Upper (D 7) (R 7) [6,96,288,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14523 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14524 : Route 9 := (fun mask => (mask,id))

def c14524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14524 : Upper (D 7) (R 7) [6,96,288,80,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80,130,128] 13 (by decide) (choices 1) [1,8] r14524 c14524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2510
  · exact u2511

def r14525 : Route 9 := (fun mask => (mask,id))

def c14525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14525 : Upper (D 7) (R 7) [6,96,288,129,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,130,1] 13 (by decide) (choices 1) [8,16] r14525 c14525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2512
  · exact u2513

def r14526 : Route 9 := (fun mask => (mask,id))

def c14526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14526 : Upper (D 7) (R 7) [6,96,288,129,130,8] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,130,8] 13 (by decide) (choices 1) [1,16] r14526 c14526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2514
  · exact u2515

def b14527 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 98 292 137 146 48 73 201 329), lower := (rows 7 98 292 137 146 48 64 128 256), losses := [] }

theorem u14527 : Upper (D 7) (R 7) [6,96,288,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14527 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14528 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 292 137 146 96 89 153 281), lower := (rows 7 98 292 137 146 96 64 128 256), losses := [] }

theorem u14528 : Upper (D 7) (R 7) [6,96,288,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14529 : Route 9 := (fun mask => (mask,id))

def c14529 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14529 : Upper (D 7) (R 7) [6,96,288,129,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,192,1] 13 (by decide) (choices 1) [2,8,16] r14529 c14529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2516
  · exact u2517
  · exact u2518

def b14530 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 292 137 208 34 89 153 281), lower := (rows 7 98 292 137 208 34 64 128 256), losses := [] }

theorem u14530 : Upper (D 7) (R 7) [6,96,288,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14531 : Route 9 := (fun mask => (mask,id))

def c14531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14531 : Upper (D 7) (R 7) [6,96,288,129,192,8] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,192,8] 13 (by decide) (choices 1) [1,2,16] r14531 c14531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2519
  · exact u2520
  · exact u2521

def b14532 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 292 137 208 48 75 139 267), lower := (rows 7 98 292 137 208 48 64 128 256), losses := [] }

theorem u14532 : Upper (D 7) (R 7) [6,96,288,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14532 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14533 : Route 9 := (fun mask => (mask,id))

def c14533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14533 : Upper (D 7) (R 7) [6,96,288,130,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,130,192,1] 13 (by decide) (choices 1) [1,8,16] r14533 c14533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2522
  · exact u2523
  · exact u2524

def b14534 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 292 138 208 40 81 145 273), lower := (rows 7 98 292 138 208 40 64 128 256), losses := [] }

theorem u14534 : Upper (D 7) (R 7) [6,96,288,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14534 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14535 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 292 138 208 48 73 137 265), lower := (rows 7 98 292 138 208 48 64 128 256), losses := [] }

theorem u14535 : Upper (D 7) (R 7) [6,96,288,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14535 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14536 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 56, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 7 98 388 25 56 33 194 194 450), lower := (rows 7 98 388 25 56 33 64 128 256), losses := [] }

theorem u14536 : Upper (D 7) (R 7) [6,96,384,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14537 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 98 388 25 56 34 193 193 449), lower := (rows 7 98 388 25 56 34 64 128 256), losses := [] }

theorem u14537 : Upper (D 7) (R 7) [6,96,384,17,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14538 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 25 56 96 195 131 387), lower := (rows 7 98 388 25 56 96 64 128 256), losses := [] }

theorem u14538 : Upper (D 7) (R 7) [6,96,384,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14539 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(2,5),(3,1),(4,1)], upper := (rows 7 98 388 25 56 160 67 195 323), lower := (rows 7 98 388 25 56 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 164 64 128 256), good := (rows 61 96 420 25 56 160 64 160 256) }] }

theorem u14539 : Upper (D 7) (R 7) [6,96,384,17,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14540 : Route 9 := (fun mask => (mask,id))

def c14540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14540 : Upper (D 7) (R 7) [6,96,384,17,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,130,1] 13 (by decide) (choices 1) [8,32] r14540 c14540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2525
  · exact u2526

theorem m14541_1 : Upper (D 7) (R 7) [6,96,384,17,130,8,1] 13 :=
  permutation_upper _ _ _ [6,96,384,17,130,1,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2525

def r14541 : Route 9 := (fun mask => (mask,id))

def c14541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14541 : Upper (D 7) (R 7) [6,96,384,17,130,8] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,130,8] 13 (by decide) (choices 1) [1,32] r14541 c14541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14541_1
  · exact u2527

def b14542 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 25 146 96 105 169 297), lower := (rows 7 98 388 25 146 96 64 128 256), losses := [] }

theorem u14542 : Upper (D 7) (R 7) [6,96,384,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14543 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 5, region := 454, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 7 98 388 25 152 33 98 226 354), lower := (rows 7 98 388 25 152 33 64 128 256), losses := [] }

theorem u14543 : Upper (D 7) (R 7) [6,96,384,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14544_1 : Upper (D 7) (R 7) [6,96,384,17,136,2,1] 13 :=
  permutation_upper _ _ _ [6,96,384,17,136,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2528

def r14544 : Route 9 := (fun mask => (mask,id))

def c14544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14544 : Upper (D 7) (R 7) [6,96,384,17,136,2] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,136,2] 13 (by decide) (choices 1) [1,32] r14544 c14544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14544_1
  · exact u2529

def b14545 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 25 152 96 99 163 291), lower := (rows 7 98 388 25 152 96 64 128 256), losses := [] }

theorem u14545 : Upper (D 7) (R 7) [6,96,384,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14546 : Route 9 := (fun mask => (mask,id))

def c14546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14546 : Upper (D 7) (R 7) [6,96,384,17,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,160,1] 13 (by decide) (choices 1) [2,8] r14546 c14546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2530
  · exact u2531

def b14547 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 452, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 7 98 388 25 176 34 73 201 329), lower := (rows 7 98 388 25 176 34 64 128 256), losses := [] }

theorem u14547 : Upper (D 7) (R 7) [6,96,384,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14548 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,5),(1,7),(2,5)], upper := (rows 7 98 388 25 176 40 67 195 323), lower := (rows 7 98 388 25 176 40 64 128 256), losses := [] }

theorem u14548 : Upper (D 7) (R 7) [6,96,384,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14548 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14549 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 25 176 96 75 139 267), lower := (rows 7 98 388 25 176 96 64 128 256), losses := [] }

theorem u14549 : Upper (D 7) (R 7) [6,96,384,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14550 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 98 388 26 49 33 200 200 456), lower := (rows 7 98 388 26 49 33 64 128 256), losses := [] }

theorem u14550 : Upper (D 7) (R 7) [6,96,384,18,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14551 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6)], upper := (rows 7 98 388 26 49 40 193 193 449), lower := (rows 7 98 388 26 49 40 64 128 256), losses := [] }

theorem u14551 : Upper (D 7) (R 7) [6,96,384,18,33,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14551 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14552 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 26 49 96 201 137 393), lower := (rows 7 98 388 26 49 96 64 128 256), losses := [] }

theorem u14552 : Upper (D 7) (R 7) [6,96,384,18,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14553 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 4, region := 74, targets := 128 }], pairs := [(0,5),(1,7),(2,5),(3,7)], upper := (rows 7 98 388 26 49 160 73 201 329), lower := (rows 7 98 388 26 49 160 64 128 256), losses := [] }

theorem u14553 : Upper (D 7) (R 7) [6,96,384,18,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14554 : Route 9 := (fun mask => (mask,id))

def c14554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14554 : Upper (D 7) (R 7) [6,96,384,18,129,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,129,1] 13 (by decide) (choices 1) [8,32] r14554 c14554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2532
  · exact u2533

theorem m14555_1 : Upper (D 7) (R 7) [6,96,384,18,129,8,1] 13 :=
  permutation_upper _ _ _ [6,96,384,18,129,1,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2532

def r14555 : Route 9 := (fun mask => (mask,id))

def c14555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14555 : Upper (D 7) (R 7) [6,96,384,18,129,8] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,129,8] 13 (by decide) (choices 1) [1,32] r14555 c14555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14555_1
  · exact u2534

def b14556 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 26 145 96 105 169 297), lower := (rows 7 98 388 26 145 96 64 128 256), losses := [] }

theorem u14556 : Upper (D 7) (R 7) [6,96,384,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14557 : Route 9 := (fun mask => (mask,id))

def c14557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14557 : Upper (D 7) (R 7) [6,96,384,18,136,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,136,1] 13 (by decide) (choices 1) [1,32] r14557 c14557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2535
  · exact u2536

def b14558 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 26 152 96 97 161 289), lower := (rows 7 98 388 26 152 96 64 128 256), losses := [] }

theorem u14558 : Upper (D 7) (R 7) [6,96,384,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14559 : Route 9 := (fun mask => (mask,id))

def c14559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14559 : Upper (D 7) (R 7) [6,96,384,18,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,160,1] 13 (by decide) (choices 1) [1,8] r14559 c14559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2537
  · exact u2538

def b14560 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(2,1),(2,5)], upper := (rows 7 98 388 26 176 40 65 193 321), lower := (rows 7 98 388 26 176 40 64 128 256), losses := [] }

theorem u14560 : Upper (D 7) (R 7) [6,96,384,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14560 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14561 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 26 176 96 73 137 265), lower := (rows 7 98 388 26 176 96 64 128 256), losses := [] }

theorem u14561 : Upper (D 7) (R 7) [6,96,384,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14562 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 388 41 81 34 216 152 408), lower := (rows 7 98 388 41 81 34 64 128 256), losses := [] }

theorem u14562 : Upper (D 7) (R 7) [6,96,384,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14563 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 388 41 81 40 210 146 402), lower := (rows 7 98 388 41 81 40 64 128 256), losses := [] }

theorem u14563 : Upper (D 7) (R 7) [6,96,384,33,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14563 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14564 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 388 41 81 48 202 138 394), lower := (rows 7 98 388 41 81 48 64 128 256), losses := [] }

theorem u14564 : Upper (D 7) (R 7) [6,96,384,33,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14564 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14565 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7),(3,1),(3,6),(4,7)], upper := (rows 7 98 388 41 81 160 90 154 282), lower := (rows 7 98 388 41 81 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 164 64 128 256), good := (rows 45 96 420 41 89 160 64 160 256) },{ target := 6, region := (rows 1 2 4 9 16 164 0 128 256), good := (rows 47 34 420 41 25 160 0 160 256) }] }

theorem u14565 : Upper (D 7) (R 7) [6,96,384,33,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14566 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 388 41 88 33 210 146 402), lower := (rows 7 98 388 41 88 33 64 128 256), losses := [] }

theorem u14566 : Upper (D 7) (R 7) [6,96,384,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14567 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 388 41 88 34 209 145 401), lower := (rows 7 98 388 41 88 34 64 128 256), losses := [] }

theorem u14567 : Upper (D 7) (R 7) [6,96,384,33,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14568 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 388 41 88 48 195 131 387), lower := (rows 7 98 388 41 88 48 64 128 256), losses := [] }

theorem u14568 : Upper (D 7) (R 7) [6,96,384,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14568 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14569 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7),(3,1),(3,6),(4,7)], upper := (rows 7 98 388 41 88 160 83 147 275), lower := (rows 7 98 388 41 88 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 164 64 128 256), good := (rows 45 96 420 41 88 160 64 160 256) },{ target := 6, region := (rows 1 2 4 9 16 164 0 128 256), good := (rows 47 34 420 41 24 160 0 160 256) }] }

theorem u14569 : Upper (D 7) (R 7) [6,96,384,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14570 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 388 41 145 34 88 216 344), lower := (rows 7 98 388 41 145 34 64 128 256), losses := [] }

theorem u14570 : Upper (D 7) (R 7) [6,96,384,33,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14571 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 388 41 145 40 82 210 338), lower := (rows 7 98 388 41 145 40 64 128 256), losses := [] }

theorem u14571 : Upper (D 7) (R 7) [6,96,384,33,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14571 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14572 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 1 },{ cop := 4, region := 40, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 7 98 388 41 145 48 74 202 330), lower := (rows 7 98 388 41 145 48 64 128 256), losses := [] }

theorem u14572 : Upper (D 7) (R 7) [6,96,384,33,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14572 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14573 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 41 145 96 90 154 282), lower := (rows 7 98 388 41 145 96 64 128 256), losses := [] }

theorem u14573 : Upper (D 7) (R 7) [6,96,384,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14574 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 388 41 146 33 88 216 344), lower := (rows 7 98 388 41 146 33 64 128 256), losses := [] }

theorem u14574 : Upper (D 7) (R 7) [6,96,384,33,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14575 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 388 41 146 40 81 209 337), lower := (rows 7 98 388 41 146 40 64 128 256), losses := [] }

theorem u14575 : Upper (D 7) (R 7) [6,96,384,33,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14575 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14576 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 452, targets := 34 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,7),(2,1),(2,5)], upper := (rows 7 98 388 41 146 48 73 201 329), lower := (rows 7 98 388 41 146 48 64 128 256), losses := [] }

theorem u14576 : Upper (D 7) (R 7) [6,96,384,33,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14576 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14577 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 41 146 96 89 153 281), lower := (rows 7 98 388 41 146 96 64 128 256), losses := [] }

theorem u14577 : Upper (D 7) (R 7) [6,96,384,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14578 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 388 41 152 33 82 210 338), lower := (rows 7 98 388 41 152 33 64 128 256), losses := [] }

theorem u14578 : Upper (D 7) (R 7) [6,96,384,33,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14579 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 388 41 152 34 81 209 337), lower := (rows 7 98 388 41 152 34 64 128 256), losses := [] }

theorem u14579 : Upper (D 7) (R 7) [6,96,384,33,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14579
end Delivery.IrregularNine14.P07
