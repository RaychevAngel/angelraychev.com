import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0112
import IrregularNine14P06C0113

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22440 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 262 25 84 40 100 228 356), lower := (rows 35 131 262 25 84 40 64 128 256), losses := [] }

theorem u22440 : Upper (D 6) (R 6) [34,129,258,17,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22440 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22441 : Route 9 := (fun mask => (mask,id))

def c22441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22441 : Upper (D 6) (R 6) [34,129,258,17,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17,68,64] 13 (by decide) (choices 1) [4,8,32] r22441 c22441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6765
  · exact u6766
  · exact u6767

def b22442 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 324, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 35 131 262 25 88 36 100 228 356), lower := (rows 35 131 262 25 88 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 47 111 175 303), good := (rows 486 486 486 508 504 484 64 128 256) }] }

theorem u22442 : Upper (D 6) (R 6) [34,129,258,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22443 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 262 25 88 96 100 164 292), lower := (rows 35 131 262 25 88 96 64 128 256), losses := [] }

theorem u22443 : Upper (D 6) (R 6) [34,129,258,17,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22444 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 131 262 25 112 36 76 204 332), lower := (rows 35 131 262 25 112 36 64 128 256), losses := [] }

theorem u22444 : Upper (D 6) (R 6) [34,129,258,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22445 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 262 25 112 40 68 196 324), lower := (rows 35 131 262 25 112 40 64 128 256), losses := [] }

theorem u22445 : Upper (D 6) (R 6) [34,129,258,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22445 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22446 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 262 25 112 96 76 140 268), lower := (rows 35 131 262 25 112 96 64 128 256), losses := [] }

theorem u22446 : Upper (D 6) (R 6) [34,129,258,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22447 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 28 56 33 68 196 324), lower := (rows 35 131 262 28 56 33 64 128 256), losses := [] }

theorem u22447 : Upper (D 6) (R 6) [34,129,258,20,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22448 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 262 28 56 36 65 193 321), lower := (rows 35 131 262 28 56 36 64 128 256), losses := [] }

theorem u22448 : Upper (D 6) (R 6) [34,129,258,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22449 : Route 9 := (fun mask => (mask,id))

def c22449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22449 : Upper (D 6) (R 6) [34,129,258,20,40,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,40,64] 13 (by decide) (choices 1) [1,4] r22449 c22449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6768
  · exact u6769

def r22450 : Route 9 := (fun mask => (mask,id))

def c22450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22450 : Upper (D 6) (R 6) [34,129,258,20,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,65,4] 13 (by decide) (choices 1) [8,32] r22450 c22450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6770
  · exact u6771

def b22451 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 324, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 262 28 81 40 100 228 356), lower := (rows 35 131 262 28 81 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 56 89 153 281), good := (rows 486 454 262 508 508 488 64 128 256) }] }

theorem u22451 : Upper (D 6) (R 6) [34,129,258,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22451 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22452 : Route 9 := (fun mask => (mask,id))

def c22452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22452 : Upper (D 6) (R 6) [34,129,258,20,65,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,65,64] 13 (by decide) (choices 1) [4,8,32] r22452 c22452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6772
  · exact u6773
  · exact u6774

def b22453 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 28 88 33 100 228 356), lower := (rows 35 131 262 28 88 33 64 128 256), losses := [] }

theorem u22453 : Upper (D 6) (R 6) [34,129,258,20,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22454 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 28 88 36 97 225 353), lower := (rows 35 131 262 28 88 36 64 128 256), losses := [] }

theorem u22454 : Upper (D 6) (R 6) [34,129,258,20,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22455 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 262 28 88 96 101 165 293), lower := (rows 35 131 262 28 88 96 64 128 256), losses := [] }

theorem u22455 : Upper (D 6) (R 6) [34,129,258,20,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22456 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 28 112 33 76 204 332), lower := (rows 35 131 262 28 112 33 64 128 256), losses := [] }

theorem u22456 : Upper (D 6) (R 6) [34,129,258,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22457 : Route 9 := (fun mask => (mask,id))

def c22457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22457 : Upper (D 6) (R 6) [34,129,258,20,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,96,4] 13 (by decide) (choices 1) [1,8] r22457 c22457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6775
  · exact u6776

def b22458 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 28 112 40 69 197 325), lower := (rows 35 131 262 28 112 40 64 128 256), losses := [] }

theorem u22458 : Upper (D 6) (R 6) [34,129,258,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22458 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22459 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 262 28 112 96 77 141 269), lower := (rows 35 131 262 28 112 96 64 128 256), losses := [] }

theorem u22459 : Upper (D 6) (R 6) [34,129,258,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22460 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 262 44 81 36 88 216 344), lower := (rows 35 131 262 44 81 36 64 128 256), losses := [] }

theorem u22460 : Upper (D 6) (R 6) [34,129,258,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22461 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 44 81 40 84 212 340), lower := (rows 35 131 262 44 81 40 64 128 256), losses := [] }

theorem u22461 : Upper (D 6) (R 6) [34,129,258,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22461 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22462 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 262 44 81 48 76 204 332), lower := (rows 35 131 262 44 81 48 64 128 256), losses := [] }

theorem u22462 : Upper (D 6) (R 6) [34,129,258,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22462 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22463 : Route 9 := (fun mask => (mask,id))

def c22463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22463 : Upper (D 6) (R 6) [34,129,258,36,65,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,36,65,64] 13 (by decide) (choices 1) [4,8,16] r22463 c22463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6777
  · exact u6778
  · exact u6779

def b22464 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 44 84 33 88 216 344), lower := (rows 35 131 262 44 84 33 64 128 256), losses := [] }

theorem u22464 : Upper (D 6) (R 6) [34,129,258,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22465 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 44 84 40 81 209 337), lower := (rows 35 131 262 44 84 40 64 128 256), losses := [] }

theorem u22465 : Upper (D 6) (R 6) [34,129,258,36,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22465 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22466 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 262 44 84 48 73 201 329), lower := (rows 35 131 262 44 84 48 64 128 256), losses := [] }

theorem u22466 : Upper (D 6) (R 6) [34,129,258,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22466 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22467 : Route 9 := (fun mask => (mask,id))

def c22467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22467 : Upper (D 6) (R 6) [34,129,258,36,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,36,68,64] 13 (by decide) (choices 1) [1,8,16] r22467 c22467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6780
  · exact u6781
  · exact u6782

def b22468 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 44 88 33 84 212 340), lower := (rows 35 131 262 44 88 33 64 128 256), losses := [] }

theorem u22468 : Upper (D 6) (R 6) [34,129,258,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22469 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 262 44 88 36 81 209 337), lower := (rows 35 131 262 44 88 36 64 128 256), losses := [] }

theorem u22469 : Upper (D 6) (R 6) [34,129,258,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22470 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 44 88 48 69 197 325), lower := (rows 35 131 262 44 88 48 64 128 256), losses := [] }

theorem u22470 : Upper (D 6) (R 6) [34,129,258,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22470 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22471 : Route 9 := (fun mask => (mask,id))

def c22471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22471 : Upper (D 6) (R 6) [34,129,258,36,72,64] 13 := by
  apply FastRouting.sound _ _ [34,129,258,36,72,64] 13 (by decide) (choices 1) [1,4,16] r22471 c22471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6783
  · exact u6784
  · exact u6785

def r22472 : Route 9 := (fun mask => (mask,id))

def c22472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22472 : Upper (D 6) (R 6) [34,129,258,48,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,258,48,65,4] 13 (by decide) (choices 1) [4,8] r22472 c22472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6786
  · exact u6787

def b22473 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 262 56 81 40 68 196 324), lower := (rows 35 131 262 56 81 40 64 128 256), losses := [] }

theorem u22473 : Upper (D 6) (R 6) [34,129,258,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22473 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22474 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 262 56 81 96 76 140 268), lower := (rows 35 131 262 56 81 96 64 128 256), losses := [] }

theorem u22474 : Upper (D 6) (R 6) [34,129,258,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22475 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 56 84 33 76 204 332), lower := (rows 35 131 262 56 84 33 64 128 256), losses := [] }

theorem u22475 : Upper (D 6) (R 6) [34,129,258,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22476 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 262 56 84 36 73 201 329), lower := (rows 35 131 262 56 84 36 64 128 256), losses := [] }

theorem u22476 : Upper (D 6) (R 6) [34,129,258,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22477 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 262 56 84 40 69 197 325), lower := (rows 35 131 262 56 84 40 64 128 256), losses := [] }

theorem u22477 : Upper (D 6) (R 6) [34,129,258,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22477 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22478 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 262 56 84 96 77 141 269), lower := (rows 35 131 262 56 84 96 64 128 256), losses := [] }

theorem u22478 : Upper (D 6) (R 6) [34,129,258,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22479 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 56 88 33 68 196 324), lower := (rows 35 131 262 56 88 33 64 128 256), losses := [] }

theorem u22479 : Upper (D 6) (R 6) [34,129,258,48,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22480 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 131 262 56 88 36 69 197 325), lower := (rows 35 131 262 56 88 36 64 128 256), losses := [] }

theorem u22480 : Upper (D 6) (R 6) [34,129,258,48,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22481 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 262 56 88 96 69 133 261), lower := (rows 35 131 262 56 88 96 64 128 256), losses := [] }

theorem u22481 : Upper (D 6) (R 6) [34,129,258,48,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22482 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 131 262 73 84 36 120 184 312), lower := (rows 35 131 262 73 84 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 11 52 52 69 133 261), good := (rows 505 457 508 457 500 500 64 128 256) }] }

theorem u22482 : Upper (D 6) (R 6) [34,129,258,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22483 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 262 73 84 40 116 180 308), lower := (rows 35 131 262 73 84 40 64 128 256), losses := [] }

theorem u22483 : Upper (D 6) (R 6) [34,129,258,65,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22483 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22484 : Route 9 := (fun mask => (mask,id))

def c22484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22484 : Upper (D 6) (R 6) [34,129,258,65,68,16] 13 := by
  apply FastRouting.sound _ _ [34,129,258,65,68,16] 13 (by decide) (choices 1) [4,8,32] r22484 c22484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6788
  · exact u6789
  · exact u6790

def r22485 : Route 9 := (fun mask => (mask,id))

def c22485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22485 : Upper (D 6) (R 6) [34,129,258,65,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,258,65,96,4] 13 (by decide) (choices 1) [4,8,16] r22485 c22485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6791
  · exact u6792
  · exact u6793

def b22486 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 262 73 112 40 84 148 276), lower := (rows 35 131 262 73 112 40 64 128 256), losses := [] }

theorem u22486 : Upper (D 6) (R 6) [34,129,258,65,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22486 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22487 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 73 112 48 76 140 268), lower := (rows 35 131 262 73 112 48 64 128 256), losses := [] }

theorem u22487 : Upper (D 6) (R 6) [34,129,258,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22487 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22488 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 262 76 112 33 92 156 284), lower := (rows 35 131 262 76 112 33 64 128 256), losses := [] }

theorem u22488 : Upper (D 6) (R 6) [34,129,258,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22489 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 262 76 112 36 89 153 281), lower := (rows 35 131 262 76 112 36 64 128 256), losses := [] }

theorem u22489 : Upper (D 6) (R 6) [34,129,258,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22490 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 262 76 112 40 85 149 277), lower := (rows 35 131 262 76 112 40 64 128 256), losses := [] }

theorem u22490 : Upper (D 6) (R 6) [34,129,258,68,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22490 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22491 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 76 112 48 77 141 269), lower := (rows 35 131 262 76 112 48 64 128 256), losses := [] }

theorem u22491 : Upper (D 6) (R 6) [34,129,258,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22491 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22492 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 13 22 48 96 224 352), lower := (rows 35 131 268 13 22 48 64 128 256), losses := [] }

theorem u22492 : Upper (D 6) (R 6) [34,129,264,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22492 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22493 : Route 9 := (fun mask => (mask,id))

def c22493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22493 : Upper (D 6) (R 6) [34,129,264,5,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,6,64] 13 (by decide) (choices 1) [16,32] r22493 c22493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6794
  · exact u6795

def b22494 : PairBound 9 := { available := 80, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 13 52 34 80 208 336), lower := (rows 35 131 268 13 52 34 64 128 256), losses := [] }

theorem u22494 : Upper (D 6) (R 6) [34,129,264,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22495 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 13 52 48 66 194 322), lower := (rows 35 131 268 13 52 48 64 128 256), losses := [] }

theorem u22495 : Upper (D 6) (R 6) [34,129,264,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22495 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22496 : Route 9 := (fun mask => (mask,id))

def c22496 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22496 : Upper (D 6) (R 6) [34,129,264,5,36,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,36,64] 13 (by decide) (choices 1) [2,16] r22496 c22496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6796
  · exact u6797

def b22497 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 268 13 82 36 112 240 368), lower := (rows 35 131 268 13 82 36 64 128 256), losses := [] }

theorem u22497 : Upper (D 6) (R 6) [34,129,264,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22498 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 13 82 48 100 228 356), lower := (rows 35 131 268 13 82 48 64 128 256), losses := [] }

theorem u22498 : Upper (D 6) (R 6) [34,129,264,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22498 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22499 : Route 9 := (fun mask => (mask,id))

def c22499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22499 : Upper (D 6) (R 6) [34,129,264,5,66,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,66,64] 13 (by decide) (choices 1) [4,16,32] r22499 c22499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6798
  · exact u6799
  · exact u6800

#print axioms u22499
end Delivery.IrregularNine14.P06
