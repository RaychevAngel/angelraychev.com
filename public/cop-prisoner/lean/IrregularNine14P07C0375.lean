import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0114

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r22500 : Route 9 := (fun mask => (mask,id))

def c22500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22500 : Upper (D 7) (R 7) [36,40,192,257,66,2] 13 := by
  apply FastRouting.sound _ _ [36,40,192,257,66,2] 13 (by decide) (choices 1) [1,16,128] r22500 c22500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6853
  · exact u6854
  · exact u6855

def r22501 : Route 9 := (fun mask => (mask,id))

def c22501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22501 : Upper (D 7) (R 7) [36,40,192,257,66,16] 13 := by
  apply FastRouting.sound _ _ [36,40,192,257,66,16] 13 (by decide) (choices 1) [1,2,128] r22501 c22501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6856
  · exact u6857
  · exact u6858

def b22502 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 42 196 265 82 160 83 147 275), lower := (rows 37 42 196 265 82 160 64 128 256), losses := [] }

theorem u22502 : Upper (D 7) (R 7) [36,40,192,257,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22503 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 42 196 266 81 33 210 146 402), lower := (rows 37 42 196 266 81 33 64 128 256), losses := [] }

theorem u22503 : Upper (D 7) (R 7) [36,40,192,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22504 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 42, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 196 266 81 34 209 145 401), lower := (rows 37 42 196 266 81 34 64 128 256), losses := [] }

theorem u22504 : Upper (D 7) (R 7) [36,40,192,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22505 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 42 196 266 81 48 195 131 387), lower := (rows 37 42 196 266 81 48 64 128 256), losses := [] }

theorem u22505 : Upper (D 7) (R 7) [36,40,192,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22505 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22506 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 42 196 266 81 160 83 147 275), lower := (rows 37 42 196 266 81 160 64 128 256), losses := [] }

theorem u22506 : Upper (D 7) (R 7) [36,40,192,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22507 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 42 196 266 82 33 209 145 401), lower := (rows 37 42 196 266 82 33 64 128 256), losses := [] }

theorem u22507 : Upper (D 7) (R 7) [36,40,192,258,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22508 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 37 42 196 266 82 48 193 129 385), lower := (rows 37 42 196 266 82 48 64 128 256), losses := [] }

theorem u22508 : Upper (D 7) (R 7) [36,40,192,258,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22508 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22509 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 42 196 266 82 160 81 145 273), lower := (rows 37 42 196 266 82 160 64 128 256), losses := [] }

theorem u22509 : Upper (D 7) (R 7) [36,40,192,258,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22510 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 196 280 19 33 194 194 450), lower := (rows 37 42 196 280 19 33 64 128 256), losses := [] }

theorem u22510 : Upper (D 7) (R 7) [36,40,192,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22511 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 42 196 280 19 34 193 193 449), lower := (rows 37 42 196 280 19 34 64 128 256), losses := [] }

theorem u22511 : Upper (D 7) (R 7) [36,40,192,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22512 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 42 196 280 19 96 195 131 387), lower := (rows 37 42 196 280 19 96 64 128 256), losses := [] }

theorem u22512 : Upper (D 7) (R 7) [36,40,192,272,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22513 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 42 196 280 81 33 194 130 386), lower := (rows 37 42 196 280 81 33 64 128 256), losses := [] }

theorem u22513 : Upper (D 7) (R 7) [36,40,192,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22514 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 37 42 196 280 81 34 195 131 387), lower := (rows 37 42 196 280 81 34 64 128 256), losses := [] }

theorem u22514 : Upper (D 7) (R 7) [36,40,192,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22515 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 42 196 280 81 160 67 131 259), lower := (rows 37 42 196 280 81 160 64 128 256), losses := [] }

theorem u22515 : Upper (D 7) (R 7) [36,40,192,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22516 : Route 9 := (fun mask => (mask,id))

def c22516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22516 : Upper (D 7) (R 7) [36,40,192,272,66,1] 13 := by
  apply FastRouting.sound _ _ [36,40,192,272,66,1] 13 (by decide) (choices 1) [1,2,128] r22516 c22516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6859
  · exact u6860
  · exact u6861

def b22517 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 42 196 280 82 34 193 129 385), lower := (rows 37 42 196 280 82 34 64 128 256), losses := [] }

theorem u22517 : Upper (D 7) (R 7) [36,40,192,272,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22518 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 42 196 280 82 160 67 131 259), lower := (rows 37 42 196 280 82 160 64 128 256), losses := [] }

theorem u22518 : Upper (D 7) (R 7) [36,40,192,272,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22519 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 42 196 328 19 33 210 146 402), lower := (rows 37 42 196 328 19 33 64 128 256), losses := [] }

theorem u22519 : Upper (D 7) (R 7) [36,40,192,320,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22520 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 42 196 328 19 34 209 145 401), lower := (rows 37 42 196 328 19 34 64 128 256), losses := [] }

theorem u22520 : Upper (D 7) (R 7) [36,40,192,320,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22521 : Route 9 := (fun mask => (mask,id))

def c22521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22521 : Upper (D 7) (R 7) [36,40,192,320,3,16] 13 := by
  apply FastRouting.sound _ _ [36,40,192,320,3,16] 13 (by decide) (choices 1) [1,2,128] r22521 c22521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6862
  · exact u6863
  · exact u6864

def b22522 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 42 196 328 19 160 83 147 275), lower := (rows 37 42 196 328 19 160 64 128 256), losses := [] }

theorem u22522 : Upper (D 7) (R 7) [36,40,192,320,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22523 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 42 196 328 145 33 82 146 274), lower := (rows 37 42 196 328 145 33 64 128 256), losses := [] }

theorem u22523 : Upper (D 7) (R 7) [36,40,192,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22524 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(3,7)], upper := (rows 37 42 196 328 145 34 83 147 275), lower := (rows 37 42 196 328 145 34 64 128 256), losses := [] }

theorem u22524 : Upper (D 7) (R 7) [36,40,192,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22525 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 42 196 328 145 48 67 131 259), lower := (rows 37 42 196 328 145 48 64 128 256), losses := [] }

theorem u22525 : Upper (D 7) (R 7) [36,40,192,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22525 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22526 : Route 9 := (fun mask => (mask,id))

def c22526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22526 : Upper (D 7) (R 7) [36,40,192,320,130,1] 13 := by
  apply FastRouting.sound _ _ [36,40,192,320,130,1] 13 (by decide) (choices 1) [1,2,16] r22526 c22526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6865
  · exact u6866
  · exact u6867

def r22527 : Route 9 := (fun mask => (mask,id))

def c22527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22527 : Upper (D 7) (R 7) [36,40,192,320,130,2] 13 := by
  apply FastRouting.sound _ _ [36,40,192,320,130,2] 13 (by decide) (choices 1) [1,16] r22527 c22527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6868
  · exact u6869

def r22528 : Route 9 := (fun mask => (mask,id))

def c22528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22528 : Upper (D 7) (R 7) [36,40,192,320,130,16] 13 := by
  apply FastRouting.sound _ _ [36,40,192,320,130,16] 13 (by decide) (choices 1) [1,2] r22528 c22528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6870
  · exact u6871

def b22529 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 25 146 96 480 416 416), lower := (rows 37 74 7 25 146 96 64 128 256), losses := [] }

theorem u22529 : Upper (D 7) (R 7) [36,72,3,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22530 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 37 74 7 25 146 160 352 480 352), lower := (rows 37 74 7 25 146 160 64 128 256), losses := [] }

theorem u22530 : Upper (D 7) (R 7) [36,72,3,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22531 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 2, region := 481, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 37 74 7 25 146 288 224 224 480), lower := (rows 37 74 7 25 146 288 64 128 256), losses := [] }

theorem u22531 : Upper (D 7) (R 7) [36,72,3,17,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22531 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22532 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 25 274 96 224 160 416), lower := (rows 37 74 7 25 274 96 64 128 256), losses := [] }

theorem u22532 : Upper (D 7) (R 7) [36,72,3,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22533 : Route 9 := (fun mask => (mask,id))

def c22533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22533 : Upper (D 7) (R 7) [36,72,3,17,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,17,258,128] 13 (by decide) (choices 1) [32,128] r22533 c22533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6872
  · exact u6873

def b22534 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 25 400 34 224 224 480), lower := (rows 37 74 7 25 400 34 64 128 256), losses := [] }

theorem u22534 : Upper (D 7) (R 7) [36,72,3,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22535 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 25 400 96 226 162 418), lower := (rows 37 74 7 25 400 96 64 128 256), losses := [] }

theorem u22535 : Upper (D 7) (R 7) [36,72,3,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22536 : Route 9 := (fun mask => (mask,id))

def c22536 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22536 : Upper (D 7) (R 7) [36,72,3,17,384,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,17,384,128] 13 (by decide) (choices 1) [2,32] r22536 c22536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6874
  · exact u6875

def b22537 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 26 176 33 448 448 448), lower := (rows 37 74 7 26 176 33 64 128 256), losses := [] }

theorem u22537 : Upper (D 7) (R 7) [36,72,3,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22538 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 74 7 26 176 96 449 385 385), lower := (rows 37 74 7 26 176 96 64 128 256), losses := [] }

theorem u22538 : Upper (D 7) (R 7) [36,72,3,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22539 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 26 176 160 321 449 321), lower := (rows 37 74 7 26 176 160 64 128 256), losses := [] }

theorem u22539 : Upper (D 7) (R 7) [36,72,3,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22540 : Route 9 := (fun mask => (mask,id))

def c22540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22540 : Upper (D 7) (R 7) [36,72,3,18,160,256] 13 := by
  apply FastRouting.sound _ _ [36,72,3,18,160,256] 13 (by decide) (choices 1) [1,128] r22540 c22540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6876
  · exact u6877

def b22541 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 26 304 33 192 192 448), lower := (rows 37 74 7 26 304 33 64 128 256), losses := [] }

theorem u22541 : Upper (D 7) (R 7) [36,72,3,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22542 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 74 7 26 304 96 193 129 385), lower := (rows 37 74 7 26 304 96 64 128 256), losses := [] }

theorem u22542 : Upper (D 7) (R 7) [36,72,3,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22543 : Route 9 := (fun mask => (mask,id))

def c22543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22543 : Upper (D 7) (R 7) [36,72,3,18,288,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,18,288,128] 13 (by decide) (choices 1) [1,128] r22543 c22543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6878
  · exact u6879

def b22544 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 26 400 33 224 224 480), lower := (rows 37 74 7 26 400 33 64 128 256), losses := [] }

theorem u22544 : Upper (D 7) (R 7) [36,72,3,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22545 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 74 7 26 400 96 225 161 417), lower := (rows 37 74 7 26 400 96 64 128 256), losses := [] }

theorem u22545 : Upper (D 7) (R 7) [36,72,3,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22546 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(0,6),(2,6),(4,1)], upper := (rows 37 74 7 26 400 160 97 225 353), lower := (rows 37 74 7 26 400 160 64 128 256), losses := [{ target := 6, region := (rows 9 2 14 8 16 176 0 128 256), good := (rows 37 15 7 63 432 160 0 160 256) }] }

theorem u22546 : Upper (D 7) (R 7) [36,72,3,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22547 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 56 146 33 448 448 448), lower := (rows 37 74 7 56 146 33 64 128 256), losses := [] }

theorem u22547 : Upper (D 7) (R 7) [36,72,3,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22548 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 481, targets := 2 },{ cop := 2, region := 400, targets := 32 }], pairs := [(0,1),(0,7),(2,7),(4,5)], upper := (rows 37 74 7 56 146 96 449 385 385), lower := (rows 37 74 7 56 146 96 64 128 256), losses := [] }

theorem u22548 : Upper (D 7) (R 7) [36,72,3,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22549 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 74 7 56 146 160 321 449 321), lower := (rows 37 74 7 56 146 160 64 128 256), losses := [] }

theorem u22549 : Upper (D 7) (R 7) [36,72,3,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22550 : Route 9 := (fun mask => (mask,id))

def c22550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22550 : Upper (D 7) (R 7) [36,72,3,48,130,256] 13 := by
  apply FastRouting.sound _ _ [36,72,3,48,130,256] 13 (by decide) (choices 1) [1,128] r22550 c22550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6880
  · exact u6881

def b22551 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 7 56 208 33 450 386 386), lower := (rows 37 74 7 56 208 33 64 128 256), losses := [] }

theorem u22551 : Upper (D 7) (R 7) [36,72,3,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22552 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 56 208 34 449 385 385), lower := (rows 37 74 7 56 208 34 64 128 256), losses := [] }

theorem u22552 : Upper (D 7) (R 7) [36,72,3,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22553 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 74 7 56 208 160 323 387 259), lower := (rows 37 74 7 56 208 160 64 128 256), losses := [] }

theorem u22553 : Upper (D 7) (R 7) [36,72,3,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22554 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 208, targets := 32 }], pairs := [(0,6),(2,6),(4,5)], upper := (rows 37 74 7 56 208 288 195 131 387), lower := (rows 37 74 7 56 208 288 64 128 256), losses := [] }

theorem u22554 : Upper (D 7) (R 7) [36,72,3,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22554 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22555 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 56 274 33 192 192 448), lower := (rows 37 74 7 56 274 33 64 128 256), losses := [] }

theorem u22555 : Upper (D 7) (R 7) [36,72,3,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22556 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 225, targets := 2 },{ cop := 2, region := 400, targets := 32 }], pairs := [(0,1),(0,7),(2,7),(4,5)], upper := (rows 37 74 7 56 274 96 193 129 385), lower := (rows 37 74 7 56 274 96 64 128 256), losses := [] }

theorem u22556 : Upper (D 7) (R 7) [36,72,3,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22557 : Route 9 := (fun mask => (mask,id))

def c22557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22557 : Upper (D 7) (R 7) [36,72,3,48,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,48,258,128] 13 (by decide) (choices 1) [1,128] r22557 c22557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6882
  · exact u6883

def b22558 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 7 56 336 33 194 130 386), lower := (rows 37 74 7 56 336 33 64 128 256), losses := [] }

theorem u22558 : Upper (D 7) (R 7) [36,72,3,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22559 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 56 336 34 193 129 385), lower := (rows 37 74 7 56 336 34 64 128 256), losses := [] }

theorem u22559 : Upper (D 7) (R 7) [36,72,3,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22559
end Delivery.IrregularNine14.P07
