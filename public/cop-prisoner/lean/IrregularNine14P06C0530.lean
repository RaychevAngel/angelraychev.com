import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0234
import IrregularNine14P06C0235

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31800 : Route 9 := (fun mask => (mask,id))

def c31800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31800 : Upper (D 6) (R 6) [10,48,65,132,258] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,258] 13 (by decide) (choices 1) [1,4,64] r31800 c31800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14082
  · exact u14083
  · exact u14084

def r31801 : Route 9 := (fun mask => (mask,id))

def c31801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31801 : Upper (D 6) (R 6) [10,48,65,132,260] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,260] 13 (by decide) (choices 1) [1,2,64] r31801 c31801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14085
  · exact u14086
  · exact u14087

def b31802 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 140 304 103 71 199 327), lower := (rows 11 50 69 140 304 32 64 128 256), losses := [] }

theorem u31802 : Upper (D 6) (R 6) [10,48,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31803 : Route 9 := (fun mask => (mask,id))

def c31803 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31803 : Upper (D 6) (R 6) [10,48,65,132,320] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132,320] 13 (by decide) (choices 1) [1,2,4] r31803 c31803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14088
  · exact u14089
  · exact u14090

def b31804 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 69 168 19 356 324 452 324), lower := (rows 11 50 69 168 19 32 64 128 256), losses := [] }

theorem u31804 : Upper (D 6) (R 6) [10,48,65,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31805 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 69 168 21 358 326 454 326), lower := (rows 11 50 69 168 21 32 64 128 256), losses := [] }

theorem u31805 : Upper (D 6) (R 6) [10,48,65,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31806 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 69 168 22 357 325 453 325), lower := (rows 11 50 69 168 22 32 64 128 256), losses := [] }

theorem u31806 : Upper (D 6) (R 6) [10,48,65,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31807 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 16, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 11 50 69 168 81 294 326 390 262), lower := (rows 11 50 69 168 81 32 64 128 256), losses := [] }

theorem u31807 : Upper (D 6) (R 6) [10,48,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31808 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 69 168 82 293 325 389 261), lower := (rows 11 50 69 168 82 32 64 128 256), losses := [] }

theorem u31808 : Upper (D 6) (R 6) [10,48,65,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31809 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 69 168 84 295 327 391 263), lower := (rows 11 50 69 168 84 32 64 128 256), losses := [] }

theorem u31809 : Upper (D 6) (R 6) [10,48,65,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31810 : Route 9 := (fun mask => (mask,id))

def c31810 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31810 : Upper (D 6) (R 6) [10,48,65,160,257] 13 := by
  apply FastRouting.sound _ _ [10,48,65,160,257] 13 (by decide) (choices 1) [2,4,64] r31810 c31810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14091
  · exact u14092
  · exact u14093

def b31811 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 69 168 274 101 69 197 325), lower := (rows 11 50 69 168 274 32 64 128 256), losses := [] }

theorem u31811 : Upper (D 6) (R 6) [10,48,65,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31812 : Route 9 := (fun mask => (mask,id))

def c31812 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31812 : Upper (D 6) (R 6) [10,48,65,160,260] 13 := by
  apply FastRouting.sound _ _ [10,48,65,160,260] 13 (by decide) (choices 1) [1,2,4,64] r31812 c31812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14094
  · exact u14095
  · exact u14096
  · exact u14097

def r31813 : Route 9 := (fun mask => (mask,id))

def c31813 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31813 : Upper (D 6) (R 6) [10,48,65,160,320] 13 := by
  apply FastRouting.sound _ _ [10,48,65,160,320] 13 (by decide) (choices 1) [1,2,4] r31813 c31813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14098
  · exact u14099
  · exact u14100

def b31814 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 69 200 19 292 356 420 292), lower := (rows 11 50 69 200 19 32 64 128 256), losses := [] }

theorem u31814 : Upper (D 6) (R 6) [10,48,65,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31815 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(4,1),(4,5)], upper := (rows 11 50 69 200 21 294 358 422 294), lower := (rows 11 50 69 200 21 32 64 128 256), losses := [] }

theorem u31815 : Upper (D 6) (R 6) [10,48,65,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31816 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 50 69 200 22 293 357 421 293), lower := (rows 11 50 69 200 22 32 64 128 256), losses := [] }

theorem u31816 : Upper (D 6) (R 6) [10,48,65,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31817 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 200 49 294 326 390 262), lower := (rows 11 50 69 200 49 32 64 128 256), losses := [] }

theorem u31817 : Upper (D 6) (R 6) [10,48,65,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31818 : PairBound 9 := { available := 261, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 200 50 293 325 389 261), lower := (rows 11 50 69 200 50 32 64 128 256), losses := [] }

theorem u31818 : Upper (D 6) (R 6) [10,48,65,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31819 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 200 52 295 327 391 263), lower := (rows 11 50 69 200 52 32 64 128 256), losses := [] }

theorem u31819 : Upper (D 6) (R 6) [10,48,65,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31820 : Route 9 := (fun mask => (mask,id))

def c31820 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31820 : Upper (D 6) (R 6) [10,48,65,192,257] 13 := by
  apply FastRouting.sound _ _ [10,48,65,192,257] 13 (by decide) (choices 1) [2,4] r31820 c31820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14101
  · exact u14102

def b31821 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 50 69 200 274 37 101 165 293), lower := (rows 11 50 69 200 274 32 64 128 256), losses := [] }

theorem u31821 : Upper (D 6) (R 6) [10,48,65,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31822 : Route 9 := (fun mask => (mask,id))

def c31822 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31822 : Upper (D 6) (R 6) [10,48,65,192,260] 13 := by
  apply FastRouting.sound _ _ [10,48,65,192,260] 13 (by decide) (choices 1) [1,2,4] r31822 c31822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14103
  · exact u14104
  · exact u14105

def b31823 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 200 304 39 71 135 263), lower := (rows 11 50 69 200 304 32 64 128 256), losses := [] }

theorem u31823 : Upper (D 6) (R 6) [10,48,65,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31824 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 69 392 19 100 100 228 356), lower := (rows 11 50 69 392 19 32 64 128 256), losses := [] }

theorem u31824 : Upper (D 6) (R 6) [10,48,65,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31825 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 69 392 21 102 102 230 358), lower := (rows 11 50 69 392 21 32 64 128 256), losses := [] }

theorem u31825 : Upper (D 6) (R 6) [10,48,65,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31826 : Route 9 := (fun mask => (mask,id))

def c31826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31826 : Upper (D 6) (R 6) [10,48,65,384,6] 13 := by
  apply FastRouting.sound _ _ [10,48,65,384,6] 13 (by decide) (choices 1) [1,4,64] r31826 c31826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14106
  · exact u14107
  · exact u14108

def b31827 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 392 49 102 70 198 326), lower := (rows 11 50 69 392 49 32 64 128 256), losses := [] }

theorem u31827 : Upper (D 6) (R 6) [10,48,65,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31828 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 69 392 50 101 69 197 325), lower := (rows 11 50 69 392 50 32 64 128 256), losses := [] }

theorem u31828 : Upper (D 6) (R 6) [10,48,65,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31829 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 392 52 103 71 199 327), lower := (rows 11 50 69 392 52 32 64 128 256), losses := [] }

theorem u31829 : Upper (D 6) (R 6) [10,48,65,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31830 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 11 50 69 392 81 38 102 166 294), lower := (rows 11 50 69 392 81 32 64 128 256), losses := [] }

theorem u31830 : Upper (D 6) (R 6) [10,48,65,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31831 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 424, targets := 64 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 11 50 69 392 82 37 101 165 293), lower := (rows 11 50 69 392 82 32 64 128 256), losses := [] }

theorem u31831 : Upper (D 6) (R 6) [10,48,65,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31832 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 69 392 84 39 103 167 295), lower := (rows 11 50 69 392 84 32 64 128 256), losses := [] }

theorem u31832 : Upper (D 6) (R 6) [10,48,65,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31833 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 69 392 112 39 71 135 263), lower := (rows 11 50 69 392 112 32 64 128 256), losses := [] }

theorem u31833 : Upper (D 6) (R 6) [10,48,65,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31834 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 70 44 21 481 449 449 449), lower := (rows 11 50 70 44 21 32 64 128 256), losses := [] }

theorem u31834 : Upper (D 6) (R 6) [10,48,66,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31835 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 50 70 44 81 421 453 389 389), lower := (rows 11 50 70 44 81 32 64 128 256), losses := [] }

theorem u31835 : Upper (D 6) (R 6) [10,48,66,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31836 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 70 44 84 417 449 385 385), lower := (rows 11 50 70 44 84 32 64 128 256), losses := [] }

theorem u31836 : Upper (D 6) (R 6) [10,48,66,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31837 : Route 9 := (fun mask => (mask,id))

def c31837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31837 : Upper (D 6) (R 6) [10,48,66,36,129] 13 := by
  apply FastRouting.sound _ _ [10,48,66,36,129] 13 (by decide) (choices 1) [1,4,64,256] r31837 c31837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14109
  · exact u14110
  · exact u14111
  · exact u14112

def r31838 : Route 9 := (fun mask => (mask,id))

def c31838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31838 : Upper (D 6) (R 6) [10,48,66,36,132] 13 := by
  apply FastRouting.sound _ _ [10,48,66,36,132] 13 (by decide) (choices 1) [1,64,256] r31838 c31838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14113
  · exact u14114
  · exact u14115

def b31839 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 297, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 50 70 44 208 293 325 389 261), lower := (rows 11 50 70 44 208 32 64 128 256), losses := [] }

theorem u31839 : Upper (D 6) (R 6) [10,48,66,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31840 : Route 9 := (fun mask => (mask,id))

def c31840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31840 : Upper (D 6) (R 6) [10,48,66,36,384] 13 := by
  apply FastRouting.sound _ _ [10,48,66,36,384] 13 (by decide) (choices 1) [1,4,64] r31840 c31840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14116
  · exact u14117
  · exact u14118

def b31841 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 488, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 70 104 21 421 453 389 389), lower := (rows 11 50 70 104 21 32 64 128 256), losses := [] }

theorem u31841 : Upper (D 6) (R 6) [10,48,66,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31842 : Route 9 := (fun mask => (mask,id))

def c31842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31842 : Upper (D 6) (R 6) [10,48,66,96,129] 13 := by
  apply FastRouting.sound _ _ [10,48,66,96,129] 13 (by decide) (choices 1) [1,4,256] r31842 c31842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14119
  · exact u14120
  · exact u14121

def r31843 : Route 9 := (fun mask => (mask,id))

def c31843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31843 : Upper (D 6) (R 6) [10,48,66,96,132] 13 := by
  apply FastRouting.sound _ _ [10,48,66,96,132] 13 (by decide) (choices 1) [1,4,256] r31843 c31843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14122
  · exact u14123
  · exact u14124

def r31844 : Route 9 := (fun mask => (mask,id))

def c31844 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31844 : Upper (D 6) (R 6) [10,48,66,96,384] 13 := by
  apply FastRouting.sound _ _ [10,48,66,96,384] 13 (by decide) (choices 1) [1,4] r31844 c31844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14125
  · exact u14126

def b31845 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 50 70 137 21 356 356 484 356), lower := (rows 11 50 70 137 21 32 64 128 256), losses := [] }

theorem u31845 : Upper (D 6) (R 6) [10,48,66,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31846 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 137 49 356 324 452 324), lower := (rows 11 50 70 137 49 32 64 128 256), losses := [] }

theorem u31846 : Upper (D 6) (R 6) [10,48,66,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31847 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 137 52 357 325 453 325), lower := (rows 11 50 70 137 52 32 64 128 256), losses := [] }

theorem u31847 : Upper (D 6) (R 6) [10,48,66,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31848 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 294, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 50 70 137 81 292 356 420 292), lower := (rows 11 50 70 137 81 32 64 128 256), losses := [] }

theorem u31848 : Upper (D 6) (R 6) [10,48,66,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31849 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 70 137 84 293 357 421 293), lower := (rows 11 50 70 137 84 32 64 128 256), losses := [] }

theorem u31849 : Upper (D 6) (R 6) [10,48,66,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31850 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 137 112 293 325 389 261), lower := (rows 11 50 70 137 112 32 64 128 256), losses := [] }

theorem u31850 : Upper (D 6) (R 6) [10,48,66,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31851 : Route 9 := (fun mask => (mask,id))

def c31851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31851 : Upper (D 6) (R 6) [10,48,66,129,257] 13 := by
  apply FastRouting.sound _ _ [10,48,66,129,257] 13 (by decide) (choices 1) [4,64] r31851 c31851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14127
  · exact u14128

def r31852 : Route 9 := (fun mask => (mask,id))

def c31852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31852 : Upper (D 6) (R 6) [10,48,66,129,260] 13 := by
  apply FastRouting.sound _ _ [10,48,66,129,260] 13 (by decide) (choices 1) [1,4,64] r31852 c31852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14129
  · exact u14130
  · exact u14131

def b31853 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 137 304 101 69 197 325), lower := (rows 11 50 70 137 304 32 64 128 256), losses := [] }

theorem u31853 : Upper (D 6) (R 6) [10,48,66,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31854 : Route 9 := (fun mask => (mask,id))

def c31854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31854 : Upper (D 6) (R 6) [10,48,66,129,320] 13 := by
  apply FastRouting.sound _ _ [10,48,66,129,320] 13 (by decide) (choices 1) [1,4] r31854 c31854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14132
  · exact u14133

def r31855 : Route 9 := (fun mask => (mask,id))

def c31855 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31855 : Upper (D 6) (R 6) [10,48,66,132,5] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,5] 13 (by decide) (choices 1) [1,64,256] r31855 c31855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14134
  · exact u14135
  · exact u14136

def b31856 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 140 49 357 325 453 325), lower := (rows 11 50 70 140 49 32 64 128 256), losses := [] }

theorem u31856 : Upper (D 6) (R 6) [10,48,66,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31857 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 140 52 353 321 449 321), lower := (rows 11 50 70 140 52 32 64 128 256), losses := [] }

theorem u31857 : Upper (D 6) (R 6) [10,48,66,132,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31858 : Route 9 := (fun mask => (mask,id))

def c31858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31858 : Upper (D 6) (R 6) [10,48,66,132,65] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,65] 13 (by decide) (choices 1) [1,4,256] r31858 c31858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14137
  · exact u14138
  · exact u14139

def b31859 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 70 140 84 289 353 417 289), lower := (rows 11 50 70 140 84 32 64 128 256), losses := [] }

theorem u31859 : Upper (D 6) (R 6) [10,48,66,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u31859
end Delivery.IrregularNine14.P06
