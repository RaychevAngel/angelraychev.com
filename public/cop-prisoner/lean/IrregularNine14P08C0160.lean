import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0041
import IrregularNine14P08C0042

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9600 : PairBound 9 := { available := 193, camps := [], pairs := [(1,5)], upper := (rows 35 262 44 25 112 225 193 193 449), lower := (rows 35 262 44 25 112 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 73 137 265), good := (rows 451 262 462 473 80 0 64 128 256) }] }

theorem u9600 : Upper (D 8) (R 8) [34,260,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9601 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9601 : Upper (D 8) (R 8) [34,260,40,17,192] 13 := by
  apply FastRouting.sound _ _ [34,260,40,17,192] 13 (by decide) (choices 1) [1,64] r9601 c9601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2480
  · exact u2481

def b9602 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 44 73 49 240 208 208 464), lower := (rows 35 262 44 73 49 32 64 128 256), losses := [] }

theorem u9602 : Upper (D 8) (R 8) [34,260,40,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9603 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 44 73 81 176 240 176 432), lower := (rows 35 262 44 73 81 32 64 128 256), losses := [] }

theorem u9603 : Upper (D 8) (R 8) [34,260,40,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9604 : Route 9 := (fun mask => (mask,id))

def c9604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9604 : Upper (D 8) (R 8) [34,260,40,65,96] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,96] 13 (by decide) (choices 1) [1,16,128] r9604 c9604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2482
  · exact u2483
  · exact u2484

def r9605 : Route 9 := (fun mask => (mask,id))

def c9605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u9605 : Upper (D 8) (R 8) [34,260,40,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,129] 13 (by decide) (choices 1) [16,64,128] r9605 c9605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2485
  · exact u2486
  · exact u2487

def r9606 : Route 9 := (fun mask => (mask,id))

def c9606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u9606 : Upper (D 8) (R 8) [34,260,40,65,160] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,160] 13 (by decide) (choices 1) [1,16,64,128] r9606 c9606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2488
  · exact u2489
  · exact u2490
  · exact u2491

def r9607 : Route 9 := (fun mask => (mask,id))

def c9607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9607 : Upper (D 8) (R 8) [34,260,40,65,192] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,192] 13 (by decide) (choices 1) [1,16,128] r9607 c9607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2492
  · exact u2493
  · exact u2494

def b9608 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 44 88 49 225 193 193 449), lower := (rows 35 262 44 88 49 32 64 128 256), losses := [] }

theorem u9608 : Upper (D 8) (R 8) [34,260,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9609 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 88 81 161 225 161 417), lower := (rows 35 262 44 88 81 32 64 128 256), losses := [] }

theorem u9609 : Upper (D 8) (R 8) [34,260,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9610 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 44 88 112 161 193 129 385), lower := (rows 35 262 44 88 112 32 64 128 256), losses := [] }

theorem u9610 : Upper (D 8) (R 8) [34,260,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9611 : Route 9 := (fun mask => (mask,id))

def c9611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9611 : Upper (D 8) (R 8) [34,260,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,40,80,129] 13 (by decide) (choices 1) [1,64,128] r9611 c9611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2495
  · exact u2496
  · exact u2497

def r9612 : Route 9 := (fun mask => (mask,id))

def c9612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9612 : Upper (D 8) (R 8) [34,260,40,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,40,80,160] 13 (by decide) (choices 1) [1,64,128] r9612 c9612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2498
  · exact u2499
  · exact u2500

def b9613 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 44 88 208 161 225 161 417), lower := (rows 35 262 44 88 208 32 64 128 256), losses := [] }

theorem u9613 : Upper (D 8) (R 8) [34,260,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9614 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 44 200 49 241 209 209 465), lower := (rows 35 262 44 200 49 32 64 128 256), losses := [] }

theorem u9614 : Upper (D 8) (R 8) [34,260,40,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9615 : Route 9 := (fun mask => (mask,id))

def c9615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9615 : Upper (D 8) (R 8) [34,260,40,192,65] 13 := by
  apply FastRouting.sound _ _ [34,260,40,192,65] 13 (by decide) (choices 1) [1,16,128] r9615 c9615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2501
  · exact u2502
  · exact u2503

def r9616 : Route 9 := (fun mask => (mask,id))

def c9616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9616 : Upper (D 8) (R 8) [34,260,40,192,96] 13 := by
  apply FastRouting.sound _ _ [34,260,40,192,96] 13 (by decide) (choices 1) [1,16,128] r9616 c9616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2504
  · exact u2505
  · exact u2506

def b9617 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 44 200 208 49 113 177 305), lower := (rows 35 262 44 200 208 32 64 128 256), losses := [] }

theorem u9617 : Upper (D 8) (R 8) [34,260,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9618 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 25 56 224 224 224 480), lower := (rows 35 262 69 25 56 32 64 128 256), losses := [] }

theorem u9618 : Upper (D 8) (R 8) [34,260,65,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9619 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 25 88 160 224 160 416), lower := (rows 35 262 69 25 88 32 64 128 256), losses := [] }

theorem u9619 : Upper (D 8) (R 8) [34,260,65,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9620 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 69 25 112 168 232 168 424), lower := (rows 35 262 69 25 112 32 64 128 256), losses := [] }

theorem u9620 : Upper (D 8) (R 8) [34,260,65,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9621 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 35 262 69 25 152 224 224 224 480), lower := (rows 35 262 69 25 152 32 64 128 256), losses := [] }

theorem u9621 : Upper (D 8) (R 8) [34,260,65,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9622 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 69 25 176 232 232 232 488), lower := (rows 35 262 69 25 176 32 64 128 256), losses := [] }

theorem u9622 : Upper (D 8) (R 8) [34,260,65,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9623 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 69 25 208 168 232 168 424), lower := (rows 35 262 69 25 208 32 64 128 256), losses := [] }

theorem u9623 : Upper (D 8) (R 8) [34,260,65,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9624 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 41 56 240 208 208 464), lower := (rows 35 262 69 41 56 32 64 128 256), losses := [] }

theorem u9624 : Upper (D 8) (R 8) [34,260,65,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9625 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 41 88 176 240 176 432), lower := (rows 35 262 69 41 88 32 64 128 256), losses := [] }

theorem u9625 : Upper (D 8) (R 8) [34,260,65,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9626 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 41 112 184 216 152 408), lower := (rows 35 262 69 41 112 32 64 128 256), losses := [] }

theorem u9626 : Upper (D 8) (R 8) [34,260,65,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9627 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 41 152 240 240 240 496), lower := (rows 35 262 69 41 152 32 64 128 256), losses := [] }

theorem u9627 : Upper (D 8) (R 8) [34,260,65,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9628 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 41 176 248 216 216 472), lower := (rows 35 262 69 41 176 32 64 128 256), losses := [] }

theorem u9628 : Upper (D 8) (R 8) [34,260,65,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9629 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 41 208 184 248 184 440), lower := (rows 35 262 69 41 208 32 64 128 256), losses := [] }

theorem u9629 : Upper (D 8) (R 8) [34,260,65,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9630 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 56 56 225 193 193 449), lower := (rows 35 262 69 56 56 32 64 128 256), losses := [] }

theorem u9630 : Upper (D 8) (R 8) [34,260,65,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9631 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 69 56 81 168 232 168 424), lower := (rows 35 262 69 56 81 32 64 128 256), losses := [] }

theorem u9631 : Upper (D 8) (R 8) [34,260,65,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9632 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 56 88 161 225 161 417), lower := (rows 35 262 69 56 88 32 64 128 256), losses := [] }

theorem u9632 : Upper (D 8) (R 8) [34,260,65,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9633 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 56 112 169 201 137 393), lower := (rows 35 262 69 56 112 32 64 128 256), losses := [] }

theorem u9633 : Upper (D 8) (R 8) [34,260,65,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9634 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 56 145 232 232 232 488), lower := (rows 35 262 69 56 145 32 64 128 256), losses := [] }

theorem u9634 : Upper (D 8) (R 8) [34,260,65,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9635 : Route 9 := (fun mask => (mask,id))

def c9635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9635 : Upper (D 8) (R 8) [34,260,65,48,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,136] 13 (by decide) (choices 1) [1,64,128] r9635 c9635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2507
  · exact u2508
  · exact u2509

def b9636 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 56 176 233 201 201 457), lower := (rows 35 262 69 56 176 32 64 128 256), losses := [] }

theorem u9636 : Upper (D 8) (R 8) [34,260,65,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9637 : Route 9 := (fun mask => (mask,id))

def c9637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9637 : Upper (D 8) (R 8) [34,260,65,48,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,192] 13 (by decide) (choices 1) [1,8,128] r9637 c9637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2510
  · exact u2511
  · exact u2512

def b9638 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 73 152 176 240 176 432), lower := (rows 35 262 69 73 152 32 64 128 256), losses := [] }

theorem u9638 : Upper (D 8) (R 8) [34,260,65,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9639 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 73 176 184 248 184 440), lower := (rows 35 262 69 73 176 32 64 128 256), losses := [] }

theorem u9639 : Upper (D 8) (R 8) [34,260,65,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9640 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 88 145 168 232 168 424), lower := (rows 35 262 69 88 145 32 64 128 256), losses := [] }

theorem u9640 : Upper (D 8) (R 8) [34,260,65,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9641 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 88 152 161 225 161 417), lower := (rows 35 262 69 88 152 32 64 128 256), losses := [] }

theorem u9641 : Upper (D 8) (R 8) [34,260,65,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9642 : Route 9 := (fun mask => (mask,id))

def c9642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9642 : Upper (D 8) (R 8) [34,260,65,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,160] 13 (by decide) (choices 1) [1,8,128] r9642 c9642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2513
  · exact u2514
  · exact u2515

def b9643 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 104 145 184 248 184 440), lower := (rows 35 262 69 104 145 32 64 128 256), losses := [] }

theorem u9643 : Upper (D 8) (R 8) [34,260,65,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9644 : Route 9 := (fun mask => (mask,id))

def c9644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9644 : Upper (D 8) (R 8) [34,260,65,96,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,136] 13 (by decide) (choices 1) [1,16,128] r9644 c9644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2516
  · exact u2517
  · exact u2518

def r9645 : Route 9 := (fun mask => (mask,id))

def c9645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9645 : Upper (D 8) (R 8) [34,260,65,96,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,160] 13 (by decide) (choices 1) [1,8,16,128] r9645 c9645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2519
  · exact u2520
  · exact u2521
  · exact u2522

def b9646 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 137 152 112 112 240 368), lower := (rows 35 262 69 137 152 32 64 128 256), losses := [] }

theorem u9646 : Upper (D 8) (R 8) [34,260,65,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9647 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 69 137 176 120 120 248 376), lower := (rows 35 262 69 137 176 32 64 128 256), losses := [] }

theorem u9647 : Upper (D 8) (R 8) [34,260,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9648 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 69 137 208 56 120 184 312), lower := (rows 35 262 69 137 208 32 64 128 256), losses := [] }

theorem u9648 : Upper (D 8) (R 8) [34,260,65,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9649 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 152 152 97 97 225 353), lower := (rows 35 262 69 152 152 32 64 128 256), losses := [] }

theorem u9649 : Upper (D 8) (R 8) [34,260,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9650 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 152 176 105 105 233 361), lower := (rows 35 262 69 152 176 32 64 128 256), losses := [] }

theorem u9650 : Upper (D 8) (R 8) [34,260,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9651 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 152 208 41 105 169 297), lower := (rows 35 262 69 152 208 32 64 128 256), losses := [] }

theorem u9651 : Upper (D 8) (R 8) [34,260,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9652 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 69 168 176 121 89 217 345), lower := (rows 35 262 69 168 176 32 64 128 256), losses := [] }

theorem u9652 : Upper (D 8) (R 8) [34,260,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9653 : Route 9 := (fun mask => (mask,id))

def c9653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9653 : Upper (D 8) (R 8) [34,260,65,160,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,160,192] 13 (by decide) (choices 1) [1,8,16] r9653 c9653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2523
  · exact u2524
  · exact u2525

def b9654 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 25 49 224 224 224 480), lower := (rows 35 262 76 25 49 32 64 128 256), losses := [] }

theorem u9654 : Upper (D 8) (R 8) [34,260,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9655 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 76 25 81 160 224 160 416), lower := (rows 35 262 76 25 81 32 64 128 256), losses := [] }

theorem u9655 : Upper (D 8) (R 8) [34,260,72,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9656 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 25 112 161 225 161 417), lower := (rows 35 262 76 25 112 32 64 128 256), losses := [] }

theorem u9656 : Upper (D 8) (R 8) [34,260,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9657 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 76 25 145 224 224 224 480), lower := (rows 35 262 76 25 145 32 64 128 256), losses := [] }

theorem u9657 : Upper (D 8) (R 8) [34,260,72,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9658 : Route 9 := (fun mask => (mask,id))

def c9658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9658 : Upper (D 8) (R 8) [34,260,72,17,160] 13 := by
  apply FastRouting.sound _ _ [34,260,72,17,160] 13 (by decide) (choices 1) [1,64,128] r9658 c9658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2526
  · exact u2527
  · exact u2528

def b9659 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 25 208 161 225 161 417), lower := (rows 35 262 76 25 208 32 64 128 256), losses := [] }

theorem u9659 : Upper (D 8) (R 8) [34,260,72,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9659
end Delivery.IrregularNine14.P08
