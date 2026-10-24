import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0233
import IrregularNine14P06C0234

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31740 : Route 9 := (fun mask => (mask,id))

def c31740 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31740 : Upper (D 6) (R 6) [10,48,33,129,260] 13 := by
  apply FastRouting.sound _ _ [10,48,33,129,260] 13 (by decide) (choices 1) [2,4,64] r31740 c31740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14010
  · exact u14011
  · exact u14012

def r31741 : Route 9 := (fun mask => (mask,id))

def c31741 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31741 : Upper (D 6) (R 6) [10,48,33,129,320] 13 := by
  apply FastRouting.sound _ _ [10,48,33,129,320] 13 (by decide) (choices 1) [2,4,64] r31741 c31741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14013
  · exact u14014
  · exact u14015

def b31742 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 37 140 19 356 324 452 324), lower := (rows 11 50 37 140 19 32 64 128 256), losses := [] }

theorem u31742 : Upper (D 6) (R 6) [10,48,33,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31743 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6),(4,1),(4,5)], upper := (rows 11 50 37 140 21 354 322 450 322), lower := (rows 11 50 37 140 21 32 64 128 256), losses := [] }

theorem u31743 : Upper (D 6) (R 6) [10,48,33,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31744 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 37 140 22 353 321 449 321), lower := (rows 11 50 37 140 22 32 64 128 256), losses := [] }

theorem u31744 : Upper (D 6) (R 6) [10,48,33,132,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31745 : Route 9 := (fun mask => (mask,id))

def c31745 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31745 : Upper (D 6) (R 6) [10,48,33,132,65] 13 := by
  apply FastRouting.sound _ _ [10,48,33,132,65] 13 (by decide) (choices 1) [2,4,64,256] r31745 c31745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14016
  · exact u14017
  · exact u14018
  · exact u14019

def b31746 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 456, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 11 50 37 140 82 357 325 453 325), lower := (rows 11 50 37 140 82 32 64 128 256), losses := [] }

theorem u31746 : Upper (D 6) (R 6) [10,48,33,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31747 : Route 9 := (fun mask => (mask,id))

def c31747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31747 : Upper (D 6) (R 6) [10,48,33,132,68] 13 := by
  apply FastRouting.sound _ _ [10,48,33,132,68] 13 (by decide) (choices 1) [1,2,64,256] r31747 c31747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14020
  · exact u14021
  · exact u14022
  · exact u14023

def r31748 : Route 9 := (fun mask => (mask,id))

def c31748 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31748 : Upper (D 6) (R 6) [10,48,33,132,257] 13 := by
  apply FastRouting.sound _ _ [10,48,33,132,257] 13 (by decide) (choices 1) [2,4,64] r31748 c31748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14024
  · exact u14025
  · exact u14026

def b31749 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 11 50 37 140 274 101 69 197 325), lower := (rows 11 50 37 140 274 32 64 128 256), losses := [] }

theorem u31749 : Upper (D 6) (R 6) [10,48,33,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31750 : Route 9 := (fun mask => (mask,id))

def c31750 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31750 : Upper (D 6) (R 6) [10,48,33,132,260] 13 := by
  apply FastRouting.sound _ _ [10,48,33,132,260] 13 (by decide) (choices 1) [1,2,64] r31750 c31750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14027
  · exact u14028
  · exact u14029

def r31751 : Route 9 := (fun mask => (mask,id))

def c31751 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31751 : Upper (D 6) (R 6) [10,48,33,132,320] 13 := by
  apply FastRouting.sound _ _ [10,48,33,132,320] 13 (by decide) (choices 1) [1,2,4,64] r31751 c31751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14030
  · exact u14031
  · exact u14032
  · exact u14033

def b31752 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 37 200 19 356 324 452 324), lower := (rows 11 50 37 200 19 32 64 128 256), losses := [] }

theorem u31752 : Upper (D 6) (R 6) [10,48,33,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31753 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6),(4,1),(4,5)], upper := (rows 11 50 37 200 21 358 326 454 326), lower := (rows 11 50 37 200 21 32 64 128 256), losses := [] }

theorem u31753 : Upper (D 6) (R 6) [10,48,33,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31754 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 37 200 22 357 325 453 325), lower := (rows 11 50 37 200 22 32 64 128 256), losses := [] }

theorem u31754 : Upper (D 6) (R 6) [10,48,33,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31755 : Route 9 := (fun mask => (mask,id))

def c31755 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31755 : Upper (D 6) (R 6) [10,48,33,192,65] 13 := by
  apply FastRouting.sound _ _ [10,48,33,192,65] 13 (by decide) (choices 1) [2,4,256] r31755 c31755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14034
  · exact u14035
  · exact u14036

def b31756 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 50 37 200 82 293 325 389 261), lower := (rows 11 50 37 200 82 32 64 128 256), losses := [] }

theorem u31756 : Upper (D 6) (R 6) [10,48,33,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31757 : Route 9 := (fun mask => (mask,id))

def c31757 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31757 : Upper (D 6) (R 6) [10,48,33,192,68] 13 := by
  apply FastRouting.sound _ _ [10,48,33,192,68] 13 (by decide) (choices 1) [1,2,4,256] r31757 c31757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14037
  · exact u14038
  · exact u14039
  · exact u14040

def r31758 : Route 9 := (fun mask => (mask,id))

def c31758 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31758 : Upper (D 6) (R 6) [10,48,33,192,257] 13 := by
  apply FastRouting.sound _ _ [10,48,33,192,257] 13 (by decide) (choices 1) [2,4,64] r31758 c31758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14041
  · exact u14042
  · exact u14043

def b31759 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 11 50 37 200 274 101 69 197 325), lower := (rows 11 50 37 200 274 32 64 128 256), losses := [] }

theorem u31759 : Upper (D 6) (R 6) [10,48,33,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31760 : Route 9 := (fun mask => (mask,id))

def c31760 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31760 : Upper (D 6) (R 6) [10,48,33,192,260] 13 := by
  apply FastRouting.sound _ _ [10,48,33,192,260] 13 (by decide) (choices 1) [1,2,4,64] r31760 c31760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14044
  · exact u14045
  · exact u14046
  · exact u14047

def r31761 : Route 9 := (fun mask => (mask,id))

def c31761 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31761 : Upper (D 6) (R 6) [10,48,33,192,320] 13 := by
  apply FastRouting.sound _ _ [10,48,33,192,320] 13 (by decide) (choices 1) [1,2,4] r31761 c31761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14048
  · exact u14049
  · exact u14050

def b31762 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 37 392 19 100 68 196 324), lower := (rows 11 50 37 392 19 32 64 128 256), losses := [] }

theorem u31762 : Upper (D 6) (R 6) [10,48,33,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31763 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6),(4,1),(4,5)], upper := (rows 11 50 37 392 21 102 70 198 326), lower := (rows 11 50 37 392 21 32 64 128 256), losses := [] }

theorem u31763 : Upper (D 6) (R 6) [10,48,33,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31764 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 37 392 22 101 69 197 325), lower := (rows 11 50 37 392 22 32 64 128 256), losses := [] }

theorem u31764 : Upper (D 6) (R 6) [10,48,33,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31765 : Route 9 := (fun mask => (mask,id))

def c31765 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31765 : Upper (D 6) (R 6) [10,48,33,384,65] 13 := by
  apply FastRouting.sound _ _ [10,48,33,384,65] 13 (by decide) (choices 1) [2,4,64] r31765 c31765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14051
  · exact u14052
  · exact u14053

def b31766 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 456, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 11 50 37 392 82 101 69 197 325), lower := (rows 11 50 37 392 82 32 64 128 256), losses := [] }

theorem u31766 : Upper (D 6) (R 6) [10,48,33,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31767 : Route 9 := (fun mask => (mask,id))

def c31767 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31767 : Upper (D 6) (R 6) [10,48,33,384,68] 13 := by
  apply FastRouting.sound _ _ [10,48,33,384,68] 13 (by decide) (choices 1) [1,2,4,64] r31767 c31767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14054
  · exact u14055
  · exact u14056
  · exact u14057

def b31768 : PairBound 9 := { available := 452, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 69 44 19 484 452 452 452), lower := (rows 11 50 69 44 19 32 64 128 256), losses := [] }

theorem u31768 : Upper (D 6) (R 6) [10,48,65,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31769 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 69 44 21 482 450 450 450), lower := (rows 11 50 69 44 21 32 64 128 256), losses := [] }

theorem u31769 : Upper (D 6) (R 6) [10,48,65,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31770 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 69 44 22 481 449 449 449), lower := (rows 11 50 69 44 22 32 64 128 256), losses := [] }

theorem u31770 : Upper (D 6) (R 6) [10,48,65,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31771 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 16, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 11 50 69 44 81 422 454 390 390), lower := (rows 11 50 69 44 81 32 64 128 256), losses := [] }

theorem u31771 : Upper (D 6) (R 6) [10,48,65,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31772 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 69 44 82 421 453 389 389), lower := (rows 11 50 69 44 82 32 64 128 256), losses := [] }

theorem u31772 : Upper (D 6) (R 6) [10,48,65,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31773 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 69 44 84 419 451 387 387), lower := (rows 11 50 69 44 84 32 64 128 256), losses := [] }

theorem u31773 : Upper (D 6) (R 6) [10,48,65,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31774 : Route 9 := (fun mask => (mask,id))

def c31774 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31774 : Upper (D 6) (R 6) [10,48,65,36,129] 13 := by
  apply FastRouting.sound _ _ [10,48,65,36,129] 13 (by decide) (choices 1) [2,4,64,256] r31774 c31774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14058
  · exact u14059
  · exact u14060
  · exact u14061

def b31775 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 69 44 146 357 325 453 325), lower := (rows 11 50 69 44 146 32 64 128 256), losses := [] }

theorem u31775 : Upper (D 6) (R 6) [10,48,65,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31776 : Route 9 := (fun mask => (mask,id))

def c31776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31776 : Upper (D 6) (R 6) [10,48,65,36,132] 13 := by
  apply FastRouting.sound _ _ [10,48,65,36,132] 13 (by decide) (choices 1) [1,2,64,256] r31776 c31776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14062
  · exact u14063
  · exact u14064
  · exact u14065

def r31777 : Route 9 := (fun mask => (mask,id))

def c31777 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31777 : Upper (D 6) (R 6) [10,48,65,36,192] 13 := by
  apply FastRouting.sound _ _ [10,48,65,36,192] 13 (by decide) (choices 1) [1,2,4,256] r31777 c31777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14066
  · exact u14067
  · exact u14068
  · exact u14069

def r31778 : Route 9 := (fun mask => (mask,id))

def c31778 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31778 : Upper (D 6) (R 6) [10,48,65,36,384] 13 := by
  apply FastRouting.sound _ _ [10,48,65,36,384] 13 (by decide) (choices 1) [1,2,4,64] r31778 c31778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14070
  · exact u14071
  · exact u14072
  · exact u14073

def b31779 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 69 137 22 356 356 484 356), lower := (rows 11 50 69 137 22 32 64 128 256), losses := [] }

theorem u31779 : Upper (D 6) (R 6) [10,48,65,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31780 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 137 50 356 324 452 324), lower := (rows 11 50 69 137 50 32 64 128 256), losses := [] }

theorem u31780 : Upper (D 6) (R 6) [10,48,65,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31781 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 137 52 358 326 454 326), lower := (rows 11 50 69 137 52 32 64 128 256), losses := [] }

theorem u31781 : Upper (D 6) (R 6) [10,48,65,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31782 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 69 137 82 292 356 420 292), lower := (rows 11 50 69 137 82 32 64 128 256), losses := [] }

theorem u31782 : Upper (D 6) (R 6) [10,48,65,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31783 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 69 137 84 294 358 422 294), lower := (rows 11 50 69 137 84 32 64 128 256), losses := [] }

theorem u31783 : Upper (D 6) (R 6) [10,48,65,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31784 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 137 112 294 326 390 262), lower := (rows 11 50 69 137 112 32 64 128 256), losses := [] }

theorem u31784 : Upper (D 6) (R 6) [10,48,65,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31785 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 69 137 274 100 100 228 356), lower := (rows 11 50 69 137 274 32 64 128 256), losses := [] }

theorem u31785 : Upper (D 6) (R 6) [10,48,65,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31786 : Route 9 := (fun mask => (mask,id))

def c31786 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31786 : Upper (D 6) (R 6) [10,48,65,129,260] 13 := by
  apply FastRouting.sound _ _ [10,48,65,129,260] 13 (by decide) (choices 1) [2,4,64] r31786 c31786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14074
  · exact u14075
  · exact u14076

def b31787 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 137 304 102 70 198 326), lower := (rows 11 50 69 137 304 32 64 128 256), losses := [] }

theorem u31787 : Upper (D 6) (R 6) [10,48,65,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31788 : Route 9 := (fun mask => (mask,id))

def c31788 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31788 : Upper (D 6) (R 6) [10,48,65,129,320] 13 := by
  apply FastRouting.sound _ _ [10,48,65,129,320] 13 (by decide) (choices 1) [2,4] r31788 c31788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14077
  · exact u14078

def b31789 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 69 140 19 356 356 484 356), lower := (rows 11 50 69 140 19 32 64 128 256), losses := [] }

theorem u31789 : Upper (D 6) (R 6) [10,48,65,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31790 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 69 140 21 354 354 482 354), lower := (rows 11 50 69 140 21 32 64 128 256), losses := [] }

theorem u31790 : Upper (D 6) (R 6) [10,48,65,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31791 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 50 69 140 22 353 353 481 353), lower := (rows 11 50 69 140 22 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 69 133 261), good := (rows 491 50 481 488 498 32 64 128 256) }] }

theorem u31791 : Upper (D 6) (R 6) [10,48,65,132,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31792 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 140 49 358 326 454 326), lower := (rows 11 50 69 140 49 32 64 128 256), losses := [] }

theorem u31792 : Upper (D 6) (R 6) [10,48,65,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31793 : PairBound 9 := { available := 325, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 140 50 357 325 453 325), lower := (rows 11 50 69 140 50 32 64 128 256), losses := [] }

theorem u31793 : Upper (D 6) (R 6) [10,48,65,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31794 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 140 52 355 323 451 323), lower := (rows 11 50 69 140 52 32 64 128 256), losses := [] }

theorem u31794 : Upper (D 6) (R 6) [10,48,65,132,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31795 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 11 50 69 140 81 294 358 422 294), lower := (rows 11 50 69 140 81 32 64 128 256), losses := [] }

theorem u31795 : Upper (D 6) (R 6) [10,48,65,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31796 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 424, targets := 64 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 11 50 69 140 82 293 357 421 293), lower := (rows 11 50 69 140 82 32 64 128 256), losses := [] }

theorem u31796 : Upper (D 6) (R 6) [10,48,65,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31797 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 69 140 84 291 355 419 291), lower := (rows 11 50 69 140 84 32 64 128 256), losses := [] }

theorem u31797 : Upper (D 6) (R 6) [10,48,65,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31798 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 140 112 295 327 391 263), lower := (rows 11 50 69 140 112 32 64 128 256), losses := [] }

theorem u31798 : Upper (D 6) (R 6) [10,48,65,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31799 : Route 9 := (fun mask => (mask,id))

def c31799 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31799 : Upper (D 6) (R 6) [10,48,65,132,257] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,257] 13 (by decide) (choices 1) [2,4,64] r31799 c31799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14079
  · exact u14080
  · exact u14081

#print axioms u31799
end Delivery.IrregularNine14.P06
