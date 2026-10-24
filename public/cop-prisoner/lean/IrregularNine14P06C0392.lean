import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0120
import IrregularNine14P06C0121

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r23520 : Route 9 := (fun mask => (mask,id))

def c23520 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23520 : Upper (D 6) (R 6) [34,132,288,5,72,64] 13 := by
  apply FastRouting.sound _ _ [34,132,288,5,72,64] 13 (by decide) (choices 1) [1,2,16] r23520 c23520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7233
  · exact u7234
  · exact u7235

def b23521 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 292 25 28 33 66 194 322), lower := (rows 35 134 292 25 28 33 64 128 256), losses := [] }

theorem u23521 : Upper (D 6) (R 6) [34,132,288,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23522 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 292 25 28 34 65 193 321), lower := (rows 35 134 292 25 28 34 64 128 256), losses := [] }

theorem u23522 : Upper (D 6) (R 6) [34,132,288,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23523 : Route 9 := (fun mask => (mask,id))

def c23523 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23523 : Upper (D 6) (R 6) [34,132,288,17,12,64] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17,12,64] 13 (by decide) (choices 1) [1,2] r23523 c23523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7236
  · exact u7237

def b23524 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 292 25 82 33 76 204 332), lower := (rows 35 134 292 25 82 33 64 128 256), losses := [] }

theorem u23524 : Upper (D 6) (R 6) [34,132,288,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23525 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 292 25 82 36 73 201 329), lower := (rows 35 134 292 25 82 36 64 128 256), losses := [] }

theorem u23525 : Upper (D 6) (R 6) [34,132,288,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23526 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 292 25 82 40 69 197 325), lower := (rows 35 134 292 25 82 40 64 128 256), losses := [] }

theorem u23526 : Upper (D 6) (R 6) [34,132,288,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23526 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23527 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 3, region := 356, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 134 292 25 82 96 77 141 269), lower := (rows 35 134 292 25 82 96 64 128 256), losses := [] }

theorem u23527 : Upper (D 6) (R 6) [34,132,288,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23528 : Route 9 := (fun mask => (mask,id))

def c23528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23528 : Upper (D 6) (R 6) [34,132,288,17,68,1] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17,68,1] 13 (by decide) (choices 1) [2,8] r23528 c23528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7238
  · exact u7239

def b23529 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 292 25 84 34 73 201 329), lower := (rows 35 134 292 25 84 34 64 128 256), losses := [] }

theorem u23529 : Upper (D 6) (R 6) [34,132,288,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23530 : Route 9 := (fun mask => (mask,id))

def c23530 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23530 : Upper (D 6) (R 6) [34,132,288,17,68,8] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17,68,8] 13 (by decide) (choices 1) [1,2] r23530 c23530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7240
  · exact u7241

def r23531 : Route 9 := (fun mask => (mask,id))

def c23531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23531 : Upper (D 6) (R 6) [34,132,288,17,68,64] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17,68,64] 13 (by decide) (choices 1) [1,2,8] r23531 c23531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7242
  · exact u7243
  · exact u7244

def b23532 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 292 25 88 33 70 198 326), lower := (rows 35 134 292 25 88 33 64 128 256), losses := [] }

theorem u23532 : Upper (D 6) (R 6) [34,132,288,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23533 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 292 25 88 34 69 197 325), lower := (rows 35 134 292 25 88 34 64 128 256), losses := [] }

theorem u23533 : Upper (D 6) (R 6) [34,132,288,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23534 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 292 25 88 36 67 195 323), lower := (rows 35 134 292 25 88 36 64 128 256), losses := [] }

theorem u23534 : Upper (D 6) (R 6) [34,132,288,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23535 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 292 25 88 96 71 135 263), lower := (rows 35 134 292 25 88 96 64 128 256), losses := [] }

theorem u23535 : Upper (D 6) (R 6) [34,132,288,17,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23536 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 292 26 81 33 76 204 332), lower := (rows 35 134 292 26 81 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 33 132 292 508 113 33 64 128 256) }] }

theorem u23536 : Upper (D 6) (R 6) [34,132,288,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23537 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 292 26 81 36 73 201 329), lower := (rows 35 134 292 26 81 36 64 128 256), losses := [] }

theorem u23537 : Upper (D 6) (R 6) [34,132,288,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23538 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 292 26 81 40 69 197 325), lower := (rows 35 134 292 26 81 40 64 128 256), losses := [] }

theorem u23538 : Upper (D 6) (R 6) [34,132,288,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23538 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23539 : Route 9 := (fun mask => (mask,id))

def c23539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23539 : Upper (D 6) (R 6) [34,132,288,18,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,288,18,65,64] 13 (by decide) (choices 1) [1,4,8] r23539 c23539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7245
  · exact u7246
  · exact u7247

def r23540 : Route 9 := (fun mask => (mask,id))

def c23540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23540 : Upper (D 6) (R 6) [34,132,288,18,68,1] 13 := by
  apply FastRouting.sound _ _ [34,132,288,18,68,1] 13 (by decide) (choices 1) [1,8] r23540 c23540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7248
  · exact u7249

def b23541 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 292 26 84 40 65 193 321), lower := (rows 35 134 292 26 84 40 64 128 256), losses := [] }

theorem u23541 : Upper (D 6) (R 6) [34,132,288,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23541 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23542 : Route 9 := (fun mask => (mask,id))

def c23542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23542 : Upper (D 6) (R 6) [34,132,288,18,68,64] 13 := by
  apply FastRouting.sound _ _ [34,132,288,18,68,64] 13 (by decide) (choices 1) [1,8] r23542 c23542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7250
  · exact u7251

def b23543 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 292 26 88 33 69 197 325), lower := (rows 35 134 292 26 88 33 64 128 256), losses := [] }

theorem u23543 : Upper (D 6) (R 6) [34,132,288,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23544 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 292 26 88 36 65 193 321), lower := (rows 35 134 292 26 88 36 64 128 256), losses := [] }

theorem u23544 : Upper (D 6) (R 6) [34,132,288,18,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23545 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 292 26 88 96 69 133 261), lower := (rows 35 134 292 26 88 96 64 128 256), losses := [] }

theorem u23545 : Upper (D 6) (R 6) [34,132,288,18,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23546 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 292 28 81 33 74 202 330), lower := (rows 35 134 292 28 81 33 64 128 256), losses := [] }

theorem u23546 : Upper (D 6) (R 6) [34,132,288,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23547 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 292 28 81 34 73 201 329), lower := (rows 35 134 292 28 81 34 64 128 256), losses := [] }

theorem u23547 : Upper (D 6) (R 6) [34,132,288,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23548 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 292 28 81 40 67 195 323), lower := (rows 35 134 292 28 81 40 64 128 256), losses := [] }

theorem u23548 : Upper (D 6) (R 6) [34,132,288,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23548 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23549 : Route 9 := (fun mask => (mask,id))

def c23549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23549 : Upper (D 6) (R 6) [34,132,288,20,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,288,20,65,64] 13 (by decide) (choices 1) [1,2,8] r23549 c23549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7252
  · exact u7253
  · exact u7254

def r23550 : Route 9 := (fun mask => (mask,id))

def c23550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23550 : Upper (D 6) (R 6) [34,132,288,20,66,1] 13 := by
  apply FastRouting.sound _ _ [34,132,288,20,66,1] 13 (by decide) (choices 1) [1,8] r23550 c23550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7255
  · exact u7256

def b23551 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 292 28 82 40 65 193 321), lower := (rows 35 134 292 28 82 40 64 128 256), losses := [] }

theorem u23551 : Upper (D 6) (R 6) [34,132,288,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23551 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23552 : Route 9 := (fun mask => (mask,id))

def c23552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23552 : Upper (D 6) (R 6) [34,132,288,20,66,64] 13 := by
  apply FastRouting.sound _ _ [34,132,288,20,66,64] 13 (by decide) (choices 1) [1,8] r23552 c23552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7257
  · exact u7258

def r23553 : Route 9 := (fun mask => (mask,id))

def c23553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23553 : Upper (D 6) (R 6) [34,132,288,20,72,1] 13 := by
  apply FastRouting.sound _ _ [34,132,288,20,72,1] 13 (by decide) (choices 1) [1,2] r23553 c23553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7259
  · exact u7260

def b23554 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 292 28 88 34 65 193 321), lower := (rows 35 134 292 28 88 34 64 128 256), losses := [] }

theorem u23554 : Upper (D 6) (R 6) [34,132,288,20,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23555 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 292 28 88 96 67 131 259), lower := (rows 35 134 292 28 88 96 64 128 256), losses := [] }

theorem u23555 : Upper (D 6) (R 6) [34,132,288,20,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23556 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 292 73 82 33 92 156 284), lower := (rows 35 134 292 73 82 33 64 128 256), losses := [] }

theorem u23556 : Upper (D 6) (R 6) [34,132,288,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23557 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 292 73 82 36 89 153 281), lower := (rows 35 134 292 73 82 36 64 128 256), losses := [] }

theorem u23557 : Upper (D 6) (R 6) [34,132,288,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23558 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 134 292 73 82 40 85 149 277), lower := (rows 35 134 292 73 82 40 64 128 256), losses := [] }

theorem u23558 : Upper (D 6) (R 6) [34,132,288,65,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23558 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23559 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 292 73 82 48 77 141 269), lower := (rows 35 134 292 73 82 48 64 128 256), losses := [] }

theorem u23559 : Upper (D 6) (R 6) [34,132,288,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23559 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23560 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,5)], upper := (rows 35 134 292 73 84 33 90 154 282), lower := (rows 35 134 292 73 84 33 64 128 256), losses := [{ target := 5, region := (rows 1 22 4 41 22 0 69 133 261), good := (rows 475 470 478 457 470 457 64 128 256) }] }

theorem u23560 : Upper (D 6) (R 6) [34,132,288,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23561 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 292 73 84 34 89 153 281), lower := (rows 35 134 292 73 84 34 64 128 256), losses := [] }

theorem u23561 : Upper (D 6) (R 6) [34,132,288,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23562 : Route 9 := (fun mask => (mask,id))

def c23562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23562 : Upper (D 6) (R 6) [34,132,288,65,68,8] 13 := by
  apply FastRouting.sound _ _ [34,132,288,65,68,8] 13 (by decide) (choices 1) [1,2,16] r23562 c23562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7261
  · exact u7262
  · exact u7263

def b23563 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 292 73 84 48 75 139 267), lower := (rows 35 134 292 73 84 48 64 128 256), losses := [] }

theorem u23563 : Upper (D 6) (R 6) [34,132,288,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23563 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23564 : Route 9 := (fun mask => (mask,id))

def c23564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23564 : Upper (D 6) (R 6) [34,132,288,66,68,1] 13 := by
  apply FastRouting.sound _ _ [34,132,288,66,68,1] 13 (by decide) (choices 1) [1,8,16] r23564 c23564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7264
  · exact u7265
  · exact u7266

def b23565 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 292 74 84 40 81 145 273), lower := (rows 35 134 292 74 84 40 64 128 256), losses := [] }

theorem u23565 : Upper (D 6) (R 6) [34,132,288,66,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23565 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23566 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 292 74 84 48 73 137 265), lower := (rows 35 134 292 74 84 48 64 128 256), losses := [] }

theorem u23566 : Upper (D 6) (R 6) [34,132,288,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23566 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23567 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 324 13 26 33 112 240 368), lower := (rows 35 134 324 13 26 33 64 128 256), losses := [] }

theorem u23567 : Upper (D 6) (R 6) [34,132,320,5,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23568 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 134 324 13 26 48 97 225 353), lower := (rows 35 134 324 13 26 48 64 128 256), losses := [] }

theorem u23568 : Upper (D 6) (R 6) [34,132,320,5,10,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23568 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23569 : Route 9 := (fun mask => (mask,id))

def c23569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23569 : Upper (D 6) (R 6) [34,132,320,5,10,64] 13 := by
  apply FastRouting.sound _ _ [34,132,320,5,10,64] 13 (by decide) (choices 1) [1,16,32] r23569 c23569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7267
  · exact u7268
  · exact u7269

def b23570 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 324 13 56 33 82 210 338), lower := (rows 35 134 324 13 56 33 64 128 256), losses := [] }

theorem u23570 : Upper (D 6) (R 6) [34,132,320,5,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23571 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 13 56 34 81 209 337), lower := (rows 35 134 324 13 56 34 64 128 256), losses := [] }

theorem u23571 : Upper (D 6) (R 6) [34,132,320,5,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23572 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 134 324 13 56 48 67 195 323), lower := (rows 35 134 324 13 56 48 64 128 256), losses := [] }

theorem u23572 : Upper (D 6) (R 6) [34,132,320,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23572 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23573 : PairBound 9 := { available := 19, camps := [], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 134 324 13 56 96 83 147 275), lower := (rows 35 134 324 13 56 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 100 64 128 256), good := (rows 34 166 356 60 56 96 96 128 256) },{ target := 1, region := (rows 1 0 4 8 24 100 64 128 256), good := (rows 33 164 356 61 56 96 96 128 256) },{ target := 2, region := (rows 3 2 0 8 24 100 64 128 256), good := (rows 35 163 352 57 56 96 96 128 256) }] }

theorem u23573 : Upper (D 6) (R 6) [34,132,320,5,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23574 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 13 81 34 120 184 312), lower := (rows 35 134 324 13 81 34 64 128 256), losses := [] }

theorem u23574 : Upper (D 6) (R 6) [34,132,320,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23575 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 134 324 13 81 40 114 178 306), lower := (rows 35 134 324 13 81 40 64 128 256), losses := [] }

theorem u23575 : Upper (D 6) (R 6) [34,132,320,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23575 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23576 : Route 9 := (fun mask => (mask,id))

def c23576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23576 : Upper (D 6) (R 6) [34,132,320,5,65,16] 13 := by
  apply FastRouting.sound _ _ [34,132,320,5,65,16] 13 (by decide) (choices 1) [2,8,32] r23576 c23576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7270
  · exact u7271
  · exact u7272

def b23577 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 134 324 13 82 33 120 184 312), lower := (rows 35 134 324 13 82 33 64 128 256), losses := [] }

theorem u23577 : Upper (D 6) (R 6) [34,132,320,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23578 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 134 324 13 82 40 113 177 305), lower := (rows 35 134 324 13 82 40 64 128 256), losses := [] }

theorem u23578 : Upper (D 6) (R 6) [34,132,320,5,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23578 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23579 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 324 13 82 48 105 169 297), lower := (rows 35 134 324 13 82 48 64 128 256), losses := [] }

theorem u23579 : Upper (D 6) (R 6) [34,132,320,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23579 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23579
end Delivery.IrregularNine14.P06
