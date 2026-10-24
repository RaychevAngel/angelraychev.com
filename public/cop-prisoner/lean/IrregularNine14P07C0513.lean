import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0215
import IrregularNine14P07C0216

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30780 : Route 9 := (fun mask => (mask,id))

def c30780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30780 : Upper (D 7) (R 7) [6,40,65,17,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17,130] 13 (by decide) (choices 1) [64,128,256] r30780 c30780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12919
  · exact u12920
  · exact u12921

def b30781 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,0)], upper := (rows 7 42 69 25 176 482 450 450 450), lower := (rows 7 42 69 25 176 32 64 128 256), losses := [] }

theorem u30781 : Upper (D 7) (R 7) [6,40,65,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30782 : Route 9 := (fun mask => (mask,id))

def c30782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30782 : Upper (D 7) (R 7) [6,40,65,17,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17,192] 13 (by decide) (choices 1) [2,128,256] r30782 c30782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12922
  · exact u12923
  · exact u12924

def r30783 : Route 9 := (fun mask => (mask,id))

def c30783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30783 : Upper (D 7) (R 7) [6,40,65,17,258] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17,258] 13 (by decide) (choices 1) [64,128] r30783 c30783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12925
  · exact u12926

def b30784 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,0)], upper := (rows 7 42 69 25 304 226 194 194 450), lower := (rows 7 42 69 25 304 32 64 128 256), losses := [] }

theorem u30784 : Upper (D 7) (R 7) [6,40,65,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30785 : Route 9 := (fun mask => (mask,id))

def c30785 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30785 : Upper (D 7) (R 7) [6,40,65,17,320] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17,320] 13 (by decide) (choices 1) [2,128] r30785 c30785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12927
  · exact u12928

def r30786 : Route 9 := (fun mask => (mask,id))

def c30786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30786 : Upper (D 7) (R 7) [6,40,65,17,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17,384] 13 (by decide) (choices 1) [2,64,128] r30786 c30786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12929
  · exact u12930
  · exact u12931

def b30787 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 10, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 42 69 26 49 480 448 448 448), lower := (rows 7 42 69 26 49 32 64 128 256), losses := [] }

theorem u30787 : Upper (D 7) (R 7) [6,40,65,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30788 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 16, targets := 160 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 7 42 69 26 81 416 480 416 416), lower := (rows 7 42 69 26 81 32 64 128 256), losses := [] }

theorem u30788 : Upper (D 7) (R 7) [6,40,65,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30789 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 26 112 417 449 385 385), lower := (rows 7 42 69 26 112 32 64 128 256), losses := [] }

theorem u30789 : Upper (D 7) (R 7) [6,40,65,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30790 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 69 26 145 480 480 480 480), lower := (rows 7 42 69 26 145 32 64 128 256), losses := [] }

theorem u30790 : Upper (D 7) (R 7) [6,40,65,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30791 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 69 26 176 481 449 449 449), lower := (rows 7 42 69 26 176 32 64 128 256), losses := [] }

theorem u30791 : Upper (D 7) (R 7) [6,40,65,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30792 : Route 9 := (fun mask => (mask,id))

def c30792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30792 : Upper (D 7) (R 7) [6,40,65,18,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,192] 13 (by decide) (choices 1) [1,128,256] r30792 c30792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12932
  · exact u12933
  · exact u12934

def b30793 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 69 26 273 224 224 224 480), lower := (rows 7 42 69 26 273 32 64 128 256), losses := [] }

theorem u30793 : Upper (D 7) (R 7) [6,40,65,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30794 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 69 26 304 225 193 193 449), lower := (rows 7 42 69 26 304 32 64 128 256), losses := [] }

theorem u30794 : Upper (D 7) (R 7) [6,40,65,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30795 : Route 9 := (fun mask => (mask,id))

def c30795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30795 : Upper (D 7) (R 7) [6,40,65,18,320] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,320] 13 (by decide) (choices 1) [1,128] r30795 c30795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12935
  · exact u12936

def r30796 : Route 9 := (fun mask => (mask,id))

def c30796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30796 : Upper (D 7) (R 7) [6,40,65,18,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18,384] 13 (by decide) (choices 1) [1,64,128] r30796 c30796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12937
  · exact u12938
  · exact u12939

def b30797 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,5),(4,7)], upper := (rows 7 42 69 88 19 416 480 416 416), lower := (rows 7 42 69 88 19 32 64 128 256), losses := [] }

theorem u30797 : Upper (D 7) (R 7) [6,40,65,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30798 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 4, region := 458, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,0)], upper := (rows 7 42 69 88 49 418 450 386 386), lower := (rows 7 42 69 88 49 32 64 128 256), losses := [] }

theorem u30798 : Upper (D 7) (R 7) [6,40,65,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30799 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 69 88 50 417 449 385 385), lower := (rows 7 42 69 88 50 32 64 128 256), losses := [] }

theorem u30799 : Upper (D 7) (R 7) [6,40,65,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30800 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 432, targets := 64 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,6)], upper := (rows 7 42 69 88 145 418 482 418 418), lower := (rows 7 42 69 88 145 32 64 128 256), losses := [] }

theorem u30800 : Upper (D 7) (R 7) [6,40,65,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30801 : Route 9 := (fun mask => (mask,id))

def c30801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30801 : Upper (D 7) (R 7) [6,40,65,80,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,80,130] 13 (by decide) (choices 1) [1,128,256] r30801 c30801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12940
  · exact u12941
  · exact u12942

def r30802 : Route 9 := (fun mask => (mask,id))

def c30802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30802 : Upper (D 7) (R 7) [6,40,65,80,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,80,160] 13 (by decide) (choices 1) [1,2,128,256] r30802 c30802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12943
  · exact u12944
  · exact u12945
  · exact u12946

def b30803 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 0, region := 432, targets := 64 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,6)], upper := (rows 7 42 69 88 273 162 226 162 418), lower := (rows 7 42 69 88 273 32 64 128 256), losses := [] }

theorem u30803 : Upper (D 7) (R 7) [6,40,65,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30804 : Route 9 := (fun mask => (mask,id))

def c30804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30804 : Upper (D 7) (R 7) [6,40,65,80,258] 13 := by
  apply FastRouting.sound _ _ [6,40,65,80,258] 13 (by decide) (choices 1) [1,128] r30804 c30804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12947
  · exact u12948

def r30805 : Route 9 := (fun mask => (mask,id))

def c30805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30805 : Upper (D 7) (R 7) [6,40,65,80,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,80,288] 13 (by decide) (choices 1) [1,2,128] r30805 c30805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12949
  · exact u12950
  · exact u12951

def r30806 : Route 9 := (fun mask => (mask,id))

def c30806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30806 : Upper (D 7) (R 7) [6,40,65,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,80,384] 13 (by decide) (choices 1) [1,2,128] r30806 c30806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12952
  · exact u12953
  · exact u12954

def b30807 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 16, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 42 69 137 50 496 464 464 464), lower := (rows 7 42 69 137 50 32 64 128 256), losses := [] }

theorem u30807 : Upper (D 7) (R 7) [6,40,65,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30808 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 137 82 432 496 432 432), lower := (rows 7 42 69 137 82 32 64 128 256), losses := [] }

theorem u30808 : Upper (D 7) (R 7) [6,40,65,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30809 : Route 9 := (fun mask => (mask,id))

def c30809 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30809 : Upper (D 7) (R 7) [6,40,65,129,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,96] 13 (by decide) (choices 1) [2,16,128,256] r30809 c30809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12955
  · exact u12956
  · exact u12957
  · exact u12958

def b30810 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 42 69 137 146 368 368 496 368), lower := (rows 7 42 69 137 146 32 64 128 256), losses := [] }

theorem u30810 : Upper (D 7) (R 7) [6,40,65,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30811 : Route 9 := (fun mask => (mask,id))

def c30811 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30811 : Upper (D 7) (R 7) [6,40,65,129,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,160] 13 (by decide) (choices 1) [2,16,64,256] r30811 c30811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12959
  · exact u12960
  · exact u12961
  · exact u12962

def r30812 : Route 9 := (fun mask => (mask,id))

def c30812 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30812 : Upper (D 7) (R 7) [6,40,65,129,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,192] 13 (by decide) (choices 1) [2,16,256] r30812 c30812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12963
  · exact u12964
  · exact u12965

def r30813 : Route 9 := (fun mask => (mask,id))

def c30813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30813 : Upper (D 7) (R 7) [6,40,65,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,258] 13 (by decide) (choices 1) [16,64,128] r30813 c30813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12966
  · exact u12967
  · exact u12968

def r30814 : Route 9 := (fun mask => (mask,id))

def c30814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30814 : Upper (D 7) (R 7) [6,40,65,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,288] 13 (by decide) (choices 1) [2,16,64,128] r30814 c30814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12969
  · exact u12970
  · exact u12971
  · exact u12972

def r30815 : Route 9 := (fun mask => (mask,id))

def c30815 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30815 : Upper (D 7) (R 7) [6,40,65,129,320] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,320] 13 (by decide) (choices 1) [2,16,128] r30815 c30815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12973
  · exact u12974
  · exact u12975

def r30816 : Route 9 := (fun mask => (mask,id))

def c30816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30816 : Upper (D 7) (R 7) [6,40,65,129,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129,384] 13 (by decide) (choices 1) [2,16,64] r30816 c30816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12976
  · exact u12977
  · exact u12978

def b30817 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 69 138 49 496 464 464 464), lower := (rows 7 42 69 138 49 32 64 128 256), losses := [] }

theorem u30817 : Upper (D 7) (R 7) [6,40,65,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30818 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 16, targets := 160 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 7 42 69 138 81 432 496 432 432), lower := (rows 7 42 69 138 81 32 64 128 256), losses := [] }

theorem u30818 : Upper (D 7) (R 7) [6,40,65,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30819 : Route 9 := (fun mask => (mask,id))

def c30819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30819 : Upper (D 7) (R 7) [6,40,65,130,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,96] 13 (by decide) (choices 1) [1,16,128,256] r30819 c30819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12979
  · exact u12980
  · exact u12981
  · exact u12982

def b30820 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 69 138 145 368 368 496 368), lower := (rows 7 42 69 138 145 32 64 128 256), losses := [] }

theorem u30820 : Upper (D 7) (R 7) [6,40,65,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30821 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 138 176 369 337 465 337), lower := (rows 7 42 69 138 176 32 64 128 256), losses := [] }

theorem u30821 : Upper (D 7) (R 7) [6,40,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30822 : Route 9 := (fun mask => (mask,id))

def c30822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30822 : Upper (D 7) (R 7) [6,40,65,130,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,192] 13 (by decide) (choices 1) [1,16,256] r30822 c30822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12983
  · exact u12984
  · exact u12985

def b30823 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 69 138 273 240 240 240 496), lower := (rows 7 42 69 138 273 32 64 128 256), losses := [] }

theorem u30823 : Upper (D 7) (R 7) [6,40,65,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30824 : Route 9 := (fun mask => (mask,id))

def c30824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30824 : Upper (D 7) (R 7) [6,40,65,130,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,288] 13 (by decide) (choices 1) [1,16,64,128] r30824 c30824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12986
  · exact u12987
  · exact u12988
  · exact u12989

def r30825 : Route 9 := (fun mask => (mask,id))

def c30825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30825 : Upper (D 7) (R 7) [6,40,65,130,320] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,320] 13 (by decide) (choices 1) [1,16,128] r30825 c30825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12990
  · exact u12991
  · exact u12992

def r30826 : Route 9 := (fun mask => (mask,id))

def c30826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30826 : Upper (D 7) (R 7) [6,40,65,130,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,384] 13 (by decide) (choices 1) [1,16,64] r30826 c30826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12993
  · exact u12994
  · exact u12995

def b30827 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 42 69 152 19 480 480 480 480), lower := (rows 7 42 69 152 19 32 64 128 256), losses := [] }

theorem u30827 : Upper (D 7) (R 7) [6,40,65,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30828 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 4, region := 458, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,0)], upper := (rows 7 42 69 152 49 482 450 450 450), lower := (rows 7 42 69 152 49 32 64 128 256), losses := [] }

theorem u30828 : Upper (D 7) (R 7) [6,40,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30829 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 69 152 50 481 449 449 449), lower := (rows 7 42 69 152 50 32 64 128 256), losses := [] }

theorem u30829 : Upper (D 7) (R 7) [6,40,65,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30830 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 7 42 69 152 81 418 482 418 418), lower := (rows 7 42 69 152 81 32 64 128 256), losses := [] }

theorem u30830 : Upper (D 7) (R 7) [6,40,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30831 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 152 82 417 481 417 417), lower := (rows 7 42 69 152 82 32 64 128 256), losses := [] }

theorem u30831 : Upper (D 7) (R 7) [6,40,65,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30832 : Route 9 := (fun mask => (mask,id))

def c30832 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30832 : Upper (D 7) (R 7) [6,40,65,144,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,96] 13 (by decide) (choices 1) [1,2,128,256] r30832 c30832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12996
  · exact u12997
  · exact u12998
  · exact u12999

def b30833 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 7 42 69 152 145 354 354 482 354), lower := (rows 7 42 69 152 145 32 64 128 256), losses := [] }

theorem u30833 : Upper (D 7) (R 7) [6,40,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30834 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 69 152 146 353 353 481 353), lower := (rows 7 42 69 152 146 32 64 128 256), losses := [] }

theorem u30834 : Upper (D 7) (R 7) [6,40,65,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30835 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 152 176 355 323 451 323), lower := (rows 7 42 69 152 176 32 64 128 256), losses := [] }

theorem u30835 : Upper (D 7) (R 7) [6,40,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30836 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 42 69 152 208 291 355 419 291), lower := (rows 7 42 69 152 208 32 64 128 256), losses := [] }

theorem u30836 : Upper (D 7) (R 7) [6,40,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30837 : Route 9 := (fun mask => (mask,id))

def c30837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30837 : Upper (D 7) (R 7) [6,40,65,144,257] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,257] 13 (by decide) (choices 1) [2,64,128] r30837 c30837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13000
  · exact u13001
  · exact u13002

def r30838 : Route 9 := (fun mask => (mask,id))

def c30838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30838 : Upper (D 7) (R 7) [6,40,65,144,258] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,258] 13 (by decide) (choices 1) [1,64,128] r30838 c30838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13003
  · exact u13004
  · exact u13005

def r30839 : Route 9 := (fun mask => (mask,id))

def c30839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30839 : Upper (D 7) (R 7) [6,40,65,144,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,288] 13 (by decide) (choices 1) [1,2,64,128] r30839 c30839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13006
  · exact u13007
  · exact u13008
  · exact u13009

#print axioms u30839
end Delivery.IrregularNine14.P07
