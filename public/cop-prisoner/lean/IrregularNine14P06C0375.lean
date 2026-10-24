import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0113

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22500 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 13 84 34 112 240 368), lower := (rows 35 131 268 13 84 34 64 128 256), losses := [] }

theorem u22500 : Upper (D 6) (R 6) [34,129,264,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22501 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 268 13 84 48 98 226 354), lower := (rows 35 131 268 13 84 48 64 128 256), losses := [] }

theorem u22501 : Upper (D 6) (R 6) [34,129,264,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22501 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22502 : Route 9 := (fun mask => (mask,id))

def c22502 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22502 : Upper (D 6) (R 6) [34,129,264,5,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,68,64] 13 (by decide) (choices 1) [2,16,32] r22502 c22502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6801
  · exact u6802
  · exact u6803

def b22503 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 13 112 34 84 212 340), lower := (rows 35 131 268 13 112 34 64 128 256), losses := [] }

theorem u22503 : Upper (D 6) (R 6) [34,129,264,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22504 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 13 112 36 82 210 338), lower := (rows 35 131 268 13 112 36 64 128 256), losses := [] }

theorem u22504 : Upper (D 6) (R 6) [34,129,264,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22505 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 13 112 48 70 198 326), lower := (rows 35 131 268 13 112 48 64 128 256), losses := [] }

theorem u22505 : Upper (D 6) (R 6) [34,129,264,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22505 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22506 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 13 112 96 86 150 278), lower := (rows 35 131 268 13 112 96 64 128 256), losses := [] }

theorem u22506 : Upper (D 6) (R 6) [34,129,264,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22507 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 268 14 21 48 96 224 352), lower := (rows 35 131 268 14 21 48 64 128 256), losses := [] }

theorem u22507 : Upper (D 6) (R 6) [34,129,264,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22507 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22508 : Route 9 := (fun mask => (mask,id))

def c22508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22508 : Upper (D 6) (R 6) [34,129,264,6,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,5,64] 13 (by decide) (choices 1) [16,32] r22508 c22508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6804
  · exact u6805

def b22509 : PairBound 9 := { available := 80, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 14 52 33 80 208 336), lower := (rows 35 131 268 14 52 33 64 128 256), losses := [] }

theorem u22509 : Upper (D 6) (R 6) [34,129,264,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22510 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 14 52 48 65 193 321), lower := (rows 35 131 268 14 52 48 64 128 256), losses := [] }

theorem u22510 : Upper (D 6) (R 6) [34,129,264,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22510 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22511 : Route 9 := (fun mask => (mask,id))

def c22511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22511 : Upper (D 6) (R 6) [34,129,264,6,36,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,36,64] 13 (by decide) (choices 1) [1,16] r22511 c22511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6806
  · exact u6807

def b22512 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 14 81 36 112 240 368), lower := (rows 35 131 268 14 81 36 64 128 256), losses := [] }

theorem u22512 : Upper (D 6) (R 6) [34,129,264,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22513 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 268 14 81 48 100 228 356), lower := (rows 35 131 268 14 81 48 64 128 256), losses := [] }

theorem u22513 : Upper (D 6) (R 6) [34,129,264,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22513 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22514 : Route 9 := (fun mask => (mask,id))

def c22514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22514 : Upper (D 6) (R 6) [34,129,264,6,65,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,65,64] 13 (by decide) (choices 1) [4,16,32] r22514 c22514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6808
  · exact u6809
  · exact u6810

def b22515 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 14 84 33 112 240 368), lower := (rows 35 131 268 14 84 33 64 128 256), losses := [] }

theorem u22515 : Upper (D 6) (R 6) [34,129,264,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22516 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 268 14 84 48 97 225 353), lower := (rows 35 131 268 14 84 48 64 128 256), losses := [] }

theorem u22516 : Upper (D 6) (R 6) [34,129,264,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22516 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22517 : Route 9 := (fun mask => (mask,id))

def c22517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22517 : Upper (D 6) (R 6) [34,129,264,6,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,68,64] 13 (by decide) (choices 1) [1,16,32] r22517 c22517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6811
  · exact u6812
  · exact u6813

def b22518 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 14 112 33 84 212 340), lower := (rows 35 131 268 14 112 33 64 128 256), losses := [] }

theorem u22518 : Upper (D 6) (R 6) [34,129,264,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22519 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 14 112 36 81 209 337), lower := (rows 35 131 268 14 112 36 64 128 256), losses := [] }

theorem u22519 : Upper (D 6) (R 6) [34,129,264,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22520 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 14 112 48 69 197 325), lower := (rows 35 131 268 14 112 48 64 128 256), losses := [] }

theorem u22520 : Upper (D 6) (R 6) [34,129,264,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22520 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22521 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 14 112 96 85 149 277), lower := (rows 35 131 268 14 112 96 64 128 256), losses := [] }

theorem u22521 : Upper (D 6) (R 6) [34,129,264,6,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22522 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 268 25 22 36 96 224 352), lower := (rows 35 131 268 25 22 36 64 128 256), losses := [] }

theorem u22522 : Upper (D 6) (R 6) [34,129,264,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22523 : Route 9 := (fun mask => (mask,id))

def c22523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22523 : Upper (D 6) (R 6) [34,129,264,17,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17,6,64] 13 (by decide) (choices 1) [4,32] r22523 c22523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6814
  · exact u6815

def b22524 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 25 52 34 68 196 324), lower := (rows 35 131 268 25 52 34 64 128 256), losses := [] }

theorem u22524 : Upper (D 6) (R 6) [34,129,264,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22525 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 268 25 52 36 66 194 322), lower := (rows 35 131 268 25 52 36 64 128 256), losses := [] }

theorem u22525 : Upper (D 6) (R 6) [34,129,264,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22526 : Route 9 := (fun mask => (mask,id))

def c22526 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22526 : Upper (D 6) (R 6) [34,129,264,17,36,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17,36,64] 13 (by decide) (choices 1) [2,4] r22526 c22526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6816
  · exact u6817

def b22527 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 268 25 82 36 100 228 356), lower := (rows 35 131 268 25 82 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 44 108 172 300), good := (rows 498 146 492 508 82 484 64 128 256) }] }

theorem u22527 : Upper (D 6) (R 6) [34,129,264,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22528 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 268 25 82 96 100 164 292), lower := (rows 35 131 268 25 82 96 64 128 256), losses := [] }

theorem u22528 : Upper (D 6) (R 6) [34,129,264,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22529 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 25 84 34 100 228 356), lower := (rows 35 131 268 25 84 34 64 128 256), losses := [] }

theorem u22529 : Upper (D 6) (R 6) [34,129,264,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22530 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 268 25 84 36 98 226 354), lower := (rows 35 131 268 25 84 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 65 129 257), good := (rows 482 450 316 508 116 36 64 128 256) }] }

theorem u22530 : Upper (D 6) (R 6) [34,129,264,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22531 : Route 9 := (fun mask => (mask,id))

def c22531 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22531 : Upper (D 6) (R 6) [34,129,264,17,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17,68,64] 13 (by decide) (choices 1) [2,4,32] r22531 c22531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6818
  · exact u6819
  · exact u6820

def b22532 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 25 112 34 68 196 324), lower := (rows 35 131 268 25 112 34 64 128 256), losses := [] }

theorem u22532 : Upper (D 6) (R 6) [34,129,264,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22533 : Route 9 := (fun mask => (mask,id))

def c22533 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22533 : Upper (D 6) (R 6) [34,129,264,17,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17,96,4] 13 (by decide) (choices 1) [2,4] r22533 c22533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6821
  · exact u6822

def b22534 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 25 112 96 70 134 262), lower := (rows 35 131 268 25 112 96 64 128 256), losses := [] }

theorem u22534 : Upper (D 6) (R 6) [34,129,264,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22535 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 268 26 21 36 96 224 352), lower := (rows 35 131 268 26 21 36 64 128 256), losses := [] }

theorem u22535 : Upper (D 6) (R 6) [34,129,264,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22536 : Route 9 := (fun mask => (mask,id))

def c22536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22536 : Upper (D 6) (R 6) [34,129,264,18,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18,5,64] 13 (by decide) (choices 1) [4,32] r22536 c22536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6823
  · exact u6824

def b22537 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 26 52 33 68 196 324), lower := (rows 35 131 268 26 52 33 64 128 256), losses := [] }

theorem u22537 : Upper (D 6) (R 6) [34,129,264,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22538 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 268 26 52 36 65 193 321), lower := (rows 35 131 268 26 52 36 64 128 256), losses := [] }

theorem u22538 : Upper (D 6) (R 6) [34,129,264,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22539 : Route 9 := (fun mask => (mask,id))

def c22539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22539 : Upper (D 6) (R 6) [34,129,264,18,36,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18,36,64] 13 (by decide) (choices 1) [1,4] r22539 c22539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6825
  · exact u6826

def b22540 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 131 268 26 81 36 100 228 356), lower := (rows 35 131 268 26 81 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 44 108 172 300), good := (rows 497 145 492 508 81 484 64 128 256) }] }

theorem u22540 : Upper (D 6) (R 6) [34,129,264,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22541 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 268 26 81 96 100 164 292), lower := (rows 35 131 268 26 81 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 112 64 128 256), good := (rows 35 131 265 59 113 96 96 128 256) }] }

theorem u22541 : Upper (D 6) (R 6) [34,129,264,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22542 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 26 84 33 100 228 356), lower := (rows 35 131 268 26 84 33 64 128 256), losses := [] }

theorem u22542 : Upper (D 6) (R 6) [34,129,264,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22543 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 26 84 36 97 225 353), lower := (rows 35 131 268 26 84 36 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 35 131 301 59 52 36 0 128 256) }] }

theorem u22543 : Upper (D 6) (R 6) [34,129,264,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22544 : Route 9 := (fun mask => (mask,id))

def c22544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22544 : Upper (D 6) (R 6) [34,129,264,18,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18,68,64] 13 (by decide) (choices 1) [1,4,32] r22544 c22544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6827
  · exact u6828
  · exact u6829

def b22545 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 26 112 33 68 196 324), lower := (rows 35 131 268 26 112 33 64 128 256), losses := [] }

theorem u22545 : Upper (D 6) (R 6) [34,129,264,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22546 : Route 9 := (fun mask => (mask,id))

def c22546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22546 : Upper (D 6) (R 6) [34,129,264,18,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18,96,4] 13 (by decide) (choices 1) [1,4] r22546 c22546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6830
  · exact u6831

def b22547 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 26 112 96 69 133 261), lower := (rows 35 131 268 26 112 96 64 128 256), losses := [] }

theorem u22547 : Upper (D 6) (R 6) [34,129,264,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22548 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 28 81 34 100 228 356), lower := (rows 35 131 268 28 81 34 64 128 256), losses := [] }

theorem u22548 : Upper (D 6) (R 6) [34,129,264,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22549 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 28 81 36 98 226 354), lower := (rows 35 131 268 28 81 36 64 128 256), losses := [] }

theorem u22549 : Upper (D 6) (R 6) [34,129,264,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22550 : Route 9 := (fun mask => (mask,id))

def c22550 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22550 : Upper (D 6) (R 6) [34,129,264,20,65,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,20,65,64] 13 (by decide) (choices 1) [2,4,32] r22550 c22550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6832
  · exact u6833
  · exact u6834

def b22551 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 28 82 33 100 228 356), lower := (rows 35 131 268 28 82 33 64 128 256), losses := [] }

theorem u22551 : Upper (D 6) (R 6) [34,129,264,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22552 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 28 82 36 97 225 353), lower := (rows 35 131 268 28 82 36 64 128 256), losses := [] }

theorem u22552 : Upper (D 6) (R 6) [34,129,264,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22553 : Route 9 := (fun mask => (mask,id))

def c22553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22553 : Upper (D 6) (R 6) [34,129,264,20,66,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,20,66,64] 13 (by decide) (choices 1) [1,4,32] r22553 c22553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6835
  · exact u6836
  · exact u6837

def b22554 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 28 112 33 70 198 326), lower := (rows 35 131 268 28 112 33 64 128 256), losses := [] }

theorem u22554 : Upper (D 6) (R 6) [34,129,264,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22555 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 28 112 34 69 197 325), lower := (rows 35 131 268 28 112 34 64 128 256), losses := [] }

theorem u22555 : Upper (D 6) (R 6) [34,129,264,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22556 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 28 112 36 67 195 323), lower := (rows 35 131 268 28 112 36 64 128 256), losses := [] }

theorem u22556 : Upper (D 6) (R 6) [34,129,264,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22557 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 28 112 96 71 135 263), lower := (rows 35 131 268 28 112 96 64 128 256), losses := [] }

theorem u22557 : Upper (D 6) (R 6) [34,129,264,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22558 : PairBound 9 := { available := 80, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 44 22 33 80 208 336), lower := (rows 35 131 268 44 22 33 64 128 256), losses := [] }

theorem u22558 : Upper (D 6) (R 6) [34,129,264,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22559 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 44 22 48 65 193 321), lower := (rows 35 131 268 44 22 48 64 128 256), losses := [] }

theorem u22559 : Upper (D 6) (R 6) [34,129,264,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22559 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22559
end Delivery.IrregularNine14.P06
