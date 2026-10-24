import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0093
import IrregularNine14P06C0094

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r19020 : Route 9 := (fun mask => (mask,id))

def c19020 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19020 : Upper (D 6) (R 6) [24,96,130,33,68,256] 13 := by
  apply FastRouting.sound _ _ [24,96,130,33,68,256] 13 (by decide) (choices 1) [1,2,4] r19020 c19020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5633
  · exact u5634
  · exact u5635

def b19021 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 98 134 41 274 33 68 196 324), lower := (rows 25 98 134 41 274 33 64 128 256), losses := [] }

theorem u19021 : Upper (D 6) (R 6) [24,96,130,33,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19022 : Route 9 := (fun mask => (mask,id))

def c19022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19022 : Upper (D 6) (R 6) [24,96,130,33,258,4] 13 := by
  apply FastRouting.sound _ _ [24,96,130,33,258,4] 13 (by decide) (choices 1) [1,4] r19022 c19022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5636
  · exact u5637

def b19023 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 41 274 96 69 133 261), lower := (rows 25 98 134 41 274 96 64 128 256), losses := [] }

theorem u19023 : Upper (D 6) (R 6) [24,96,130,33,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19024 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 98 134 41 276 33 70 198 326), lower := (rows 25 98 134 41 276 33 64 128 256), losses := [] }

theorem u19024 : Upper (D 6) (R 6) [24,96,130,33,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19025 : PairBound 9 := { available := 69, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 25 98 134 41 276 34 69 197 325), lower := (rows 25 98 134 41 276 34 64 128 256), losses := [{ target := 2, region := (rows 17 66 0 24 16 102 64 128 256), good := (rows 25 98 162 41 313 34 98 128 256) }] }

theorem u19025 : Upper (D 6) (R 6) [24,96,130,33,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19026 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 134 41 276 36 67 195 323), lower := (rows 25 98 134 41 276 36 64 128 256), losses := [] }

theorem u19026 : Upper (D 6) (R 6) [24,96,130,33,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19027 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 41 276 96 71 135 263), lower := (rows 25 98 134 41 276 96 64 128 256), losses := [] }

theorem u19027 : Upper (D 6) (R 6) [24,96,130,33,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19028 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 98 134 41 336 33 70 134 262), lower := (rows 25 98 134 41 336 33 64 128 256), losses := [] }

theorem u19028 : Upper (D 6) (R 6) [24,96,130,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19029 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 134 41 336 34 69 133 261), lower := (rows 25 98 134 41 336 34 64 128 256), losses := [] }

theorem u19029 : Upper (D 6) (R 6) [24,96,130,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19030 : Route 9 := (fun mask => (mask,id))

def c19030 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19030 : Upper (D 6) (R 6) [24,96,130,33,320,4] 13 := by
  apply FastRouting.sound _ _ [24,96,130,33,320,4] 13 (by decide) (choices 1) [1,2,4] r19030 c19030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5638
  · exact u5639
  · exact u5640

def b19031 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 134 44 84 33 323 387 259), lower := (rows 25 98 134 44 84 33 64 128 256), losses := [] }

theorem u19031 : Upper (D 6) (R 6) [24,96,130,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19032 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 98 134 44 84 34 321 385 257), lower := (rows 25 98 134 44 84 34 64 128 256), losses := [] }

theorem u19032 : Upper (D 6) (R 6) [24,96,130,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19033_1 : Upper (D 6) (R 6) [24,96,130,36,68,256,1] 13 :=
  permutation_upper _ _ _ [24,96,130,36,68,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5641

theorem m19033_2 : Upper (D 6) (R 6) [24,96,130,36,68,256,2] 13 :=
  permutation_upper _ _ _ [24,96,130,36,68,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5642

def r19033 : Route 9 := (fun mask => (mask,id))

def c19033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19033 : Upper (D 6) (R 6) [24,96,130,36,68,256] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,68,256] 13 (by decide) (choices 1) [1,2] r19033 c19033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m19033_1
  · exact m19033_2

def b19034 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 98 134 44 273 33 70 198 326), lower := (rows 25 98 134 44 273 33 64 128 256), losses := [] }

theorem u19034 : Upper (D 6) (R 6) [24,96,130,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19035 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 98 134 44 273 34 69 197 325), lower := (rows 25 98 134 44 273 34 64 128 256), losses := [] }

theorem u19035 : Upper (D 6) (R 6) [24,96,130,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19036 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 98 134 44 273 36 67 195 323), lower := (rows 25 98 134 44 273 36 64 128 256), losses := [] }

theorem u19036 : Upper (D 6) (R 6) [24,96,130,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19037 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 44 273 96 71 135 263), lower := (rows 25 98 134 44 273 96 64 128 256), losses := [] }

theorem u19037 : Upper (D 6) (R 6) [24,96,130,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19038 : Route 9 := (fun mask => (mask,id))

def c19038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19038 : Upper (D 6) (R 6) [24,96,130,36,258,1] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,258,1] 13 (by decide) (choices 1) [1,4] r19038 c19038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5643
  · exact u5644

def b19039 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 98 134 44 274 36 65 193 321), lower := (rows 25 98 134 44 274 36 64 128 256), losses := [] }

theorem u19039 : Upper (D 6) (R 6) [24,96,130,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19040 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 44 274 96 69 133 261), lower := (rows 25 98 134 44 274 96 64 128 256), losses := [] }

theorem u19040 : Upper (D 6) (R 6) [24,96,130,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19041 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 134 44 276 33 67 195 323), lower := (rows 25 98 134 44 276 33 64 128 256), losses := [] }

theorem u19041 : Upper (D 6) (R 6) [24,96,130,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19042 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 98 134 44 276 34 65 193 321), lower := (rows 25 98 134 44 276 34 64 128 256), losses := [] }

theorem u19042 : Upper (D 6) (R 6) [24,96,130,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19043 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 134 44 276 96 67 131 259), lower := (rows 25 98 134 44 276 96 64 128 256), losses := [] }

theorem u19043 : Upper (D 6) (R 6) [24,96,130,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19044 : Route 9 := (fun mask => (mask,id))

def c19044 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19044 : Upper (D 6) (R 6) [24,96,130,36,320,1] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,320,1] 13 (by decide) (choices 1) [1,2,4] r19044 c19044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5645
  · exact u5646
  · exact u5647

def b19045 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 98 134 44 336 34 69 133 261), lower := (rows 25 98 134 44 336 34 64 128 256), losses := [] }

theorem u19045 : Upper (D 6) (R 6) [24,96,130,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19046 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 98 134 44 336 36 67 131 259), lower := (rows 25 98 134 44 336 36 64 128 256), losses := [] }

theorem u19046 : Upper (D 6) (R 6) [24,96,130,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19047 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 388, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 98 164 11 21 34 324 452 324), lower := (rows 25 98 164 11 21 34 64 128 256), losses := [] }

theorem u19047 : Upper (D 6) (R 6) [24,96,160,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19048 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 7, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 98 164 11 21 36 322 450 322), lower := (rows 25 98 164 11 21 36 64 128 256), losses := [] }

theorem u19048 : Upper (D 6) (R 6) [24,96,160,3,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19049 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 164 11 21 96 326 390 262), lower := (rows 25 98 164 11 21 96 64 128 256), losses := [] }

theorem u19049 : Upper (D 6) (R 6) [24,96,160,3,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19050 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 486, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 98 164 11 21 288 70 198 326), lower := (rows 25 98 164 11 21 288 64 128 256), losses := [] }

theorem u19050 : Upper (D 6) (R 6) [24,96,160,3,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19050 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19051 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 164 11 84 33 326 390 262), lower := (rows 25 98 164 11 84 33 64 128 256), losses := [] }

theorem u19051 : Upper (D 6) (R 6) [24,96,160,3,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19052 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 164 11 84 34 325 389 261), lower := (rows 25 98 164 11 84 34 64 128 256), losses := [] }

theorem u19052 : Upper (D 6) (R 6) [24,96,160,3,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19053 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 98 164 11 84 36 323 387 259), lower := (rows 25 98 164 11 84 36 64 128 256), losses := [] }

theorem u19053 : Upper (D 6) (R 6) [24,96,160,3,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19054 : Route 9 := (fun mask => (mask,id))

def c19054 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19054 : Upper (D 6) (R 6) [24,96,160,3,68,256] 13 := by
  apply FastRouting.sound _ _ [24,96,160,3,68,256] 13 (by decide) (choices 1) [1,2,4] r19054 c19054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5648
  · exact u5649
  · exact u5650

def b19055 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 1, region := 132, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 98 164 11 273 34 68 196 324), lower := (rows 25 98 164 11 273 34 64 128 256), losses := [] }

theorem u19055 : Upper (D 6) (R 6) [24,96,160,3,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19056 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 7, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 98 164 11 273 36 70 198 326), lower := (rows 25 98 164 11 273 36 64 128 256), losses := [] }

theorem u19056 : Upper (D 6) (R 6) [24,96,160,3,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19057 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 164 11 273 96 70 134 262), lower := (rows 25 98 164 11 273 96 64 128 256), losses := [] }

theorem u19057 : Upper (D 6) (R 6) [24,96,160,3,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19058 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 164 11 276 33 70 198 326), lower := (rows 25 98 164 11 276 33 64 128 256), losses := [] }

theorem u19058 : Upper (D 6) (R 6) [24,96,160,3,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19059 : Route 9 := (fun mask => (mask,id))

def c19059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19059 : Upper (D 6) (R 6) [24,96,160,3,260,2] 13 := by
  apply FastRouting.sound _ _ [24,96,160,3,260,2] 13 (by decide) (choices 1) [1,4] r19059 c19059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5651
  · exact u5652

def b19060 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 98 164 11 276 36 67 195 323), lower := (rows 25 98 164 11 276 36 64 128 256), losses := [] }

theorem u19060 : Upper (D 6) (R 6) [24,96,160,3,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19061 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 164 11 276 96 71 135 263), lower := (rows 25 98 164 11 276 96 64 128 256), losses := [] }

theorem u19061 : Upper (D 6) (R 6) [24,96,160,3,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19062 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 164 11 336 33 70 134 262), lower := (rows 25 98 164 11 336 33 64 128 256), losses := [] }

theorem u19062 : Upper (D 6) (R 6) [24,96,160,3,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19063 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 164 11 336 34 69 133 261), lower := (rows 25 98 164 11 336 34 64 128 256), losses := [] }

theorem u19063 : Upper (D 6) (R 6) [24,96,160,3,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19064 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 98 164 11 336 36 71 135 263), lower := (rows 25 98 164 11 336 36 64 128 256), losses := [] }

theorem u19064 : Upper (D 6) (R 6) [24,96,160,3,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19065 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 164 13 273 34 70 198 326), lower := (rows 25 98 164 13 273 34 64 128 256), losses := [] }

theorem u19065 : Upper (D 6) (R 6) [24,96,160,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19066 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 7, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 98 164 13 273 36 66 194 322), lower := (rows 25 98 164 13 273 36 64 128 256), losses := [] }

theorem u19066 : Upper (D 6) (R 6) [24,96,160,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19067 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 164 13 273 96 70 134 262), lower := (rows 25 98 164 13 273 96 64 128 256), losses := [] }

theorem u19067 : Upper (D 6) (R 6) [24,96,160,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19068 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 164 13 274 33 70 198 326), lower := (rows 25 98 164 13 274 33 64 128 256), losses := [] }

theorem u19068 : Upper (D 6) (R 6) [24,96,160,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19069 : Route 9 := (fun mask => (mask,id))

def c19069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19069 : Upper (D 6) (R 6) [24,96,160,5,258,2] 13 := by
  apply FastRouting.sound _ _ [24,96,160,5,258,2] 13 (by decide) (choices 1) [1,4] r19069 c19069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5653
  · exact u5654

def b19070 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 98 164 13 274 36 67 195 323), lower := (rows 25 98 164 13 274 36 64 128 256), losses := [] }

theorem u19070 : Upper (D 6) (R 6) [24,96,160,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19071 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 98 164 13 274 96 71 135 263), lower := (rows 25 98 164 13 274 96 64 128 256), losses := [] }

theorem u19071 : Upper (D 6) (R 6) [24,96,160,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19072 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 164 13 336 33 70 134 262), lower := (rows 25 98 164 13 336 33 64 128 256), losses := [] }

theorem u19072 : Upper (D 6) (R 6) [24,96,160,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19073 : Route 9 := (fun mask => (mask,id))

def c19073 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19073 : Upper (D 6) (R 6) [24,96,160,5,320,2] 13 := by
  apply FastRouting.sound _ _ [24,96,160,5,320,2] 13 (by decide) (choices 1) [1,2,4] r19073 c19073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5655
  · exact u5656
  · exact u5657

def b19074 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 98 164 13 336 36 67 131 259), lower := (rows 25 98 164 13 336 36 64 128 256), losses := [] }

theorem u19074 : Upper (D 6) (R 6) [24,96,160,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19075 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 98 164 14 81 33 326 390 262), lower := (rows 25 98 164 14 81 33 64 128 256), losses := [] }

theorem u19075 : Upper (D 6) (R 6) [24,96,160,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19076 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 98 164 14 81 34 325 389 261), lower := (rows 25 98 164 14 81 34 64 128 256), losses := [] }

theorem u19076 : Upper (D 6) (R 6) [24,96,160,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19077 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 337, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 98 164 14 81 36 323 387 259), lower := (rows 25 98 164 14 81 36 64 128 256), losses := [] }

theorem u19077 : Upper (D 6) (R 6) [24,96,160,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19078 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 81, targets := 32 }], pairs := [(0,5),(4,5)], upper := (rows 25 98 164 14 81 288 71 135 263), lower := (rows 25 98 164 14 81 288 64 128 256), losses := [] }

theorem u19078 : Upper (D 6) (R 6) [24,96,160,6,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19078 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19079 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 98 164 14 273 33 70 198 326), lower := (rows 25 98 164 14 273 33 64 128 256), losses := [] }

theorem u19079 : Upper (D 6) (R 6) [24,96,160,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19079
end Delivery.IrregularNine14.P06
