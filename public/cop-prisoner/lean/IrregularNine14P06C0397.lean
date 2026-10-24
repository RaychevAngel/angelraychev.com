import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0121
import IrregularNine14P06C0122

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23820 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 13 304 33 70 198 326), lower := (rows 35 138 84 13 304 33 64 128 256), losses := [] }

theorem u23820 : Upper (D 6) (R 6) [34,136,80,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23821 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 13 304 34 69 197 325), lower := (rows 35 138 84 13 304 34 64 128 256), losses := [] }

theorem u23821 : Upper (D 6) (R 6) [34,136,80,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23822 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 194, targets := 36 },{ cop := 0, region := 336, targets := 4 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 84 13 304 36 67 195 323), lower := (rows 35 138 84 13 304 36 64 128 256), losses := [] }

theorem u23822 : Upper (D 6) (R 6) [34,136,80,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23823 : Route 9 := (fun mask => (mask,id))

def c23823 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23823 : Upper (D 6) (R 6) [34,136,80,5,288,64] 13 := by
  apply FastRouting.sound _ _ [34,136,80,5,288,64] 13 (by decide) (choices 1) [1,2,4] r23823 c23823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7319
  · exact u7320
  · exact u7321

def b23824 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 14 273 33 100 228 356), lower := (rows 35 138 84 14 273 33 64 128 256), losses := [] }

theorem u23824 : Upper (D 6) (R 6) [34,136,80,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23825 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 84 14 273 36 97 225 353), lower := (rows 35 138 84 14 273 36 64 128 256), losses := [] }

theorem u23825 : Upper (D 6) (R 6) [34,136,80,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23826 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 14 273 96 101 165 293), lower := (rows 35 138 84 14 273 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 100 64 128 256), good := (rows 35 139 112 43 273 96 96 128 256) }] }

theorem u23826 : Upper (D 6) (R 6) [34,136,80,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23827 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 14 304 33 69 197 325), lower := (rows 35 138 84 14 304 33 64 128 256), losses := [] }

theorem u23827 : Upper (D 6) (R 6) [34,136,80,6,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23828 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 84 14 304 36 65 193 321), lower := (rows 35 138 84 14 304 36 64 128 256), losses := [] }

theorem u23828 : Upper (D 6) (R 6) [34,136,80,6,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23829 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 14 304 96 69 133 261), lower := (rows 35 138 84 14 304 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 100 64 128 256), good := (rows 35 139 112 43 304 96 96 128 256) }] }

theorem u23829 : Upper (D 6) (R 6) [34,136,80,6,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23830 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 44 273 33 70 198 326), lower := (rows 35 138 84 44 273 33 64 128 256), losses := [] }

theorem u23830 : Upper (D 6) (R 6) [34,136,80,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23831 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 44 273 34 69 197 325), lower := (rows 35 138 84 44 273 34 64 128 256), losses := [] }

theorem u23831 : Upper (D 6) (R 6) [34,136,80,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23832 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 84 44 273 36 67 195 323), lower := (rows 35 138 84 44 273 36 64 128 256), losses := [] }

theorem u23832 : Upper (D 6) (R 6) [34,136,80,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23833 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 138 84 44 273 96 71 135 263), lower := (rows 35 138 84 44 273 96 64 128 256), losses := [] }

theorem u23833 : Upper (D 6) (R 6) [34,136,80,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23834 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 44 274 33 69 197 325), lower := (rows 35 138 84 44 274 33 64 128 256), losses := [] }

theorem u23834 : Upper (D 6) (R 6) [34,136,80,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23835 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 84 44 274 36 65 193 321), lower := (rows 35 138 84 44 274 36 64 128 256), losses := [] }

theorem u23835 : Upper (D 6) (R 6) [34,136,80,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23836 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 138 84 44 274 96 69 133 261), lower := (rows 35 138 84 44 274 96 64 128 256), losses := [] }

theorem u23836 : Upper (D 6) (R 6) [34,136,80,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23837 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 73 22 33 356 420 292), lower := (rows 35 138 84 73 22 33 64 128 256), losses := [] }

theorem u23837 : Upper (D 6) (R 6) [34,136,80,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23838 : PairBound 9 := { available := 289, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 73 22 36 353 417 289), lower := (rows 35 138 84 73 22 36 64 128 256), losses := [] }

theorem u23838 : Upper (D 6) (R 6) [34,136,80,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23839 : Route 9 := (fun mask => (mask,id))

def c23839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23839 : Upper (D 6) (R 6) [34,136,80,65,6,256] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,6,256] 13 (by decide) (choices 1) [1,4,32] r23839 c23839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7322
  · exact u7323
  · exact u7324

def b23840 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 73 52 33 326 390 262), lower := (rows 35 138 84 73 52 33 64 128 256), losses := [] }

theorem u23840 : Upper (D 6) (R 6) [34,136,80,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23841 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 73 52 34 325 389 261), lower := (rows 35 138 84 73 52 34 64 128 256), losses := [] }

theorem u23841 : Upper (D 6) (R 6) [34,136,80,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23842 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 84 73 52 36 323 387 259), lower := (rows 35 138 84 73 52 36 64 128 256), losses := [] }

theorem u23842 : Upper (D 6) (R 6) [34,136,80,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23843 : Route 9 := (fun mask => (mask,id))

def c23843 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23843 : Upper (D 6) (R 6) [34,136,80,65,36,256] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,36,256] 13 (by decide) (choices 1) [1,2,4] r23843 c23843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7325
  · exact u7326
  · exact u7327

def b23844 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 73 273 34 100 164 292), lower := (rows 35 138 84 73 273 34 64 128 256), losses := [] }

theorem u23844 : Upper (D 6) (R 6) [34,136,80,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23845 : Route 9 := (fun mask => (mask,id))

def c23845 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23845 : Upper (D 6) (R 6) [34,136,80,65,257,4] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,257,4] 13 (by decide) (choices 1) [2,4,32] r23845 c23845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7328
  · exact u7329
  · exact u7330

def b23846 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 73 274 33 100 164 292), lower := (rows 35 138 84 73 274 33 64 128 256), losses := [] }

theorem u23846 : Upper (D 6) (R 6) [34,136,80,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23847 : Route 9 := (fun mask => (mask,id))

def c23847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23847 : Upper (D 6) (R 6) [34,136,80,65,258,4] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,258,4] 13 (by decide) (choices 1) [1,4,32] r23847 c23847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7331
  · exact u7332
  · exact u7333

def b23848 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 73 276 33 102 166 294), lower := (rows 35 138 84 73 276 33 64 128 256), losses := [] }

theorem u23848 : Upper (D 6) (R 6) [34,136,80,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23849 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 73 276 34 101 165 293), lower := (rows 35 138 84 73 276 34 64 128 256), losses := [] }

theorem u23849 : Upper (D 6) (R 6) [34,136,80,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23850 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 73 276 36 99 163 291), lower := (rows 35 138 84 73 276 36 64 128 256), losses := [] }

theorem u23850 : Upper (D 6) (R 6) [34,136,80,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23851 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 73 304 33 70 134 262), lower := (rows 35 138 84 73 304 33 64 128 256), losses := [] }

theorem u23851 : Upper (D 6) (R 6) [34,136,80,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23852 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 73 304 34 69 133 261), lower := (rows 35 138 84 73 304 34 64 128 256), losses := [] }

theorem u23852 : Upper (D 6) (R 6) [34,136,80,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23853 : Route 9 := (fun mask => (mask,id))

def c23853 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23853 : Upper (D 6) (R 6) [34,136,80,65,288,4] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,288,4] 13 (by decide) (choices 1) [1,2,4] r23853 c23853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7334
  · exact u7335
  · exact u7336

def b23854 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 74 21 33 356 420 292), lower := (rows 35 138 84 74 21 33 64 128 256), losses := [] }

theorem u23854 : Upper (D 6) (R 6) [34,136,80,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23855 : PairBound 9 := { available := 289, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 74 21 36 353 417 289), lower := (rows 35 138 84 74 21 36 64 128 256), losses := [] }

theorem u23855 : Upper (D 6) (R 6) [34,136,80,66,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23856 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 84 74 21 288 101 165 293), lower := (rows 35 138 84 74 21 288 64 128 256), losses := [] }

theorem u23856 : Upper (D 6) (R 6) [34,136,80,66,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23856 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23857 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 74 52 33 325 389 261), lower := (rows 35 138 84 74 52 33 64 128 256), losses := [] }

theorem u23857 : Upper (D 6) (R 6) [34,136,80,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23858 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 84 74 52 36 321 385 257), lower := (rows 35 138 84 74 52 36 64 128 256), losses := [] }

theorem u23858 : Upper (D 6) (R 6) [34,136,80,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23859 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 84 74 52 288 69 133 261), lower := (rows 35 138 84 74 52 288 64 128 256), losses := [] }

theorem u23859 : Upper (D 6) (R 6) [34,136,80,66,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23859 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23860 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 74 273 33 100 164 292), lower := (rows 35 138 84 74 273 33 64 128 256), losses := [] }

theorem u23860 : Upper (D 6) (R 6) [34,136,80,66,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23861 : Route 9 := (fun mask => (mask,id))

def c23861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23861 : Upper (D 6) (R 6) [34,136,80,66,257,4] 13 := by
  apply FastRouting.sound _ _ [34,136,80,66,257,4] 13 (by decide) (choices 1) [1,4,32] r23861 c23861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7337
  · exact u7338
  · exact u7339

def b23862 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 74 276 33 101 165 293), lower := (rows 35 138 84 74 276 33 64 128 256), losses := [] }

theorem u23862 : Upper (D 6) (R 6) [34,136,80,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23863 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 74 276 36 97 161 289), lower := (rows 35 138 84 74 276 36 64 128 256), losses := [] }

theorem u23863 : Upper (D 6) (R 6) [34,136,80,66,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23864 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 74 304 33 69 133 261), lower := (rows 35 138 84 74 304 33 64 128 256), losses := [] }

theorem u23864 : Upper (D 6) (R 6) [34,136,80,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23865 : Route 9 := (fun mask => (mask,id))

def c23865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23865 : Upper (D 6) (R 6) [34,136,80,66,288,4] 13 := by
  apply FastRouting.sound _ _ [34,136,80,66,288,4] 13 (by decide) (choices 1) [1,4] r23865 c23865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7340
  · exact u7341

def b23866 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 104 21 33 326 390 262), lower := (rows 35 138 84 104 21 33 64 128 256), losses := [] }

theorem u23866 : Upper (D 6) (R 6) [34,136,80,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23867 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 104 21 34 325 389 261), lower := (rows 35 138 84 104 21 34 64 128 256), losses := [] }

theorem u23867 : Upper (D 6) (R 6) [34,136,80,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23868 : PairBound 9 := { available := 259, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 104 21 36 323 387 259), lower := (rows 35 138 84 104 21 36 64 128 256), losses := [] }

theorem u23868 : Upper (D 6) (R 6) [34,136,80,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23869 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 84 104 21 288 71 135 263), lower := (rows 35 138 84 104 21 288 64 128 256), losses := [] }

theorem u23869 : Upper (D 6) (R 6) [34,136,80,96,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23869 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23870 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 104 273 33 70 134 262), lower := (rows 35 138 84 104 273 33 64 128 256), losses := [] }

theorem u23870 : Upper (D 6) (R 6) [34,136,80,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23871 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 104 273 34 69 133 261), lower := (rows 35 138 84 104 273 34 64 128 256), losses := [] }

theorem u23871 : Upper (D 6) (R 6) [34,136,80,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23872 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 35 138 84 104 273 36 71 135 263), lower := (rows 35 138 84 104 273 36 64 128 256), losses := [] }

theorem u23872 : Upper (D 6) (R 6) [34,136,80,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23873 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 104 274 33 69 133 261), lower := (rows 35 138 84 104 274 33 64 128 256), losses := [] }

theorem u23873 : Upper (D 6) (R 6) [34,136,80,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23874 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 35 138 84 104 274 36 69 133 261), lower := (rows 35 138 84 104 274 36 64 128 256), losses := [] }

theorem u23874 : Upper (D 6) (R 6) [34,136,80,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23875 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 104 276 33 71 135 263), lower := (rows 35 138 84 104 276 33 64 128 256), losses := [] }

theorem u23875 : Upper (D 6) (R 6) [34,136,80,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23876 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 104 276 34 69 133 261), lower := (rows 35 138 84 104 276 34 64 128 256), losses := [] }

theorem u23876 : Upper (D 6) (R 6) [34,136,80,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23877 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 104 276 36 67 131 259), lower := (rows 35 138 84 104 276 36 64 128 256), losses := [] }

theorem u23877 : Upper (D 6) (R 6) [34,136,80,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23878 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 265 21 34 100 228 356), lower := (rows 35 138 84 265 21 34 64 128 256), losses := [] }

theorem u23878 : Upper (D 6) (R 6) [34,136,80,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23879 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 84 265 21 36 98 226 354), lower := (rows 35 138 84 265 21 36 64 128 256), losses := [] }

theorem u23879 : Upper (D 6) (R 6) [34,136,80,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23879
end Delivery.IrregularNine14.P06
