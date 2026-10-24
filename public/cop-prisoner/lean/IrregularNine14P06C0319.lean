import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0094
import IrregularNine14P06C0095

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19140 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 1, region := 40, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 131 262 41 84 34 100 228 356), lower := (rows 25 131 262 41 84 34 64 128 256), losses := [] }

theorem u19140 : Upper (D 6) (R 6) [24,129,258,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19141 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 131 262 41 84 36 98 226 354), lower := (rows 25 131 262 41 84 36 64 128 256), losses := [] }

theorem u19141 : Upper (D 6) (R 6) [24,129,258,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19142 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 131 262 41 84 96 102 166 294), lower := (rows 25 131 262 41 84 96 64 128 256), losses := [] }

theorem u19142 : Upper (D 6) (R 6) [24,129,258,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19143 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 131 262 42 52 33 68 196 324), lower := (rows 25 131 262 42 52 33 64 128 256), losses := [] }

theorem u19143 : Upper (D 6) (R 6) [24,129,258,34,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19144 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 131 262 42 52 36 65 193 321), lower := (rows 25 131 262 42 52 36 64 128 256), losses := [] }

theorem u19144 : Upper (D 6) (R 6) [24,129,258,34,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19145 : Route 9 := (fun mask => (mask,id))

def c19145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19145 : Upper (D 6) (R 6) [24,129,258,34,36,64] 13 := by
  apply FastRouting.sound _ _ [24,129,258,34,36,64] 13 (by decide) (choices 1) [1,4] r19145 c19145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5694
  · exact u5695

def b19146 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 40, targets := 68 },{ cop := 3, region := 324, targets := 1 }], pairs := [(2,0),(3,2),(3,6)], upper := (rows 25 131 262 42 84 33 100 228 356), lower := (rows 25 131 262 42 84 33 64 128 256), losses := [] }

theorem u19146 : Upper (D 6) (R 6) [24,129,258,34,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19147 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 40, targets := 65 }], pairs := [(0,6),(3,0),(3,6)], upper := (rows 25 131 262 42 84 36 97 225 353), lower := (rows 25 131 262 42 84 36 64 128 256), losses := [{ target := 6, region := (rows 17 2 4 12 16 52 0 128 256), good := (rows 57 131 302 42 61 44 0 128 256) }] }

theorem u19147 : Upper (D 6) (R 6) [24,129,258,34,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19148 : Route 9 := (fun mask => (mask,id))

def c19148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19148 : Upper (D 6) (R 6) [24,129,258,34,68,64] 13 := by
  apply FastRouting.sound _ _ [24,129,258,34,68,64] 13 (by decide) (choices 1) [1,4,32] r19148 c19148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5696
  · exact u5697
  · exact u5698

def b19149 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 40, targets := 4 }], pairs := [(1,5),(2,5),(3,2)], upper := (rows 25 131 262 42 112 33 68 196 324), lower := (rows 25 131 262 42 112 33 64 128 256), losses := [] }

theorem u19149 : Upper (D 6) (R 6) [24,129,258,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19150 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 25 131 262 42 112 36 69 197 325), lower := (rows 25 131 262 42 112 36 64 128 256), losses := [] }

theorem u19150 : Upper (D 6) (R 6) [24,129,258,34,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19151 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 131 262 42 112 96 69 133 261), lower := (rows 25 131 262 42 112 96 64 128 256), losses := [] }

theorem u19151 : Upper (D 6) (R 6) [24,129,258,34,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19152 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 131 262 44 84 33 98 226 354), lower := (rows 25 131 262 44 84 33 64 128 256), losses := [] }

theorem u19152 : Upper (D 6) (R 6) [24,129,258,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19153 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 40, targets := 65 },{ cop := 3, region := 81, targets := 2 }], pairs := [(0,1),(3,0),(3,6)], upper := (rows 25 131 262 44 84 34 97 225 353), lower := (rows 25 131 262 44 84 34 64 128 256), losses := [] }

theorem u19153 : Upper (D 6) (R 6) [24,129,258,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19154 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 41, targets := 2 },{ cop := 0, region := 226, targets := 4 }], pairs := [(0,1),(1,2),(3,1)], upper := (rows 25 131 262 44 84 96 99 163 291), lower := (rows 25 131 262 44 84 96 64 128 256), losses := [] }

theorem u19154 : Upper (D 6) (R 6) [24,129,258,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19155 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 324, targets := 1 }], pairs := [(1,5),(2,0),(2,5)], upper := (rows 25 131 262 44 112 33 70 198 326), lower := (rows 25 131 262 44 112 33 64 128 256), losses := [] }

theorem u19155 : Upper (D 6) (R 6) [24,129,258,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19156 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 25 131 262 44 112 34 69 197 325), lower := (rows 25 131 262 44 112 34 64 128 256), losses := [] }

theorem u19156 : Upper (D 6) (R 6) [24,129,258,36,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19157 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 131 262 44 112 36 67 195 323), lower := (rows 25 131 262 44 112 36 64 128 256), losses := [] }

theorem u19157 : Upper (D 6) (R 6) [24,129,258,36,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19158 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 131 262 44 112 96 71 135 263), lower := (rows 25 131 262 44 112 96 64 128 256), losses := [] }

theorem u19158 : Upper (D 6) (R 6) [24,129,258,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19159 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 5, region := 324, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 131 292 13 82 34 100 228 356), lower := (rows 25 131 292 13 82 34 64 128 256), losses := [] }

theorem u19159 : Upper (D 6) (R 6) [24,129,288,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19160 : PairBound 9 := { available := 98, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 13 82 36 98 226 354), lower := (rows 25 131 292 13 82 36 64 128 256), losses := [] }

theorem u19160 : Upper (D 6) (R 6) [24,129,288,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19161 : Route 9 := (fun mask => (mask,id))

def c19161 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19161 : Upper (D 6) (R 6) [24,129,288,5,66,64] 13 := by
  apply FastRouting.sound _ _ [24,129,288,5,66,64] 13 (by decide) (choices 1) [2,4,32] r19161 c19161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5699
  · exact u5700
  · exact u5701

def b19162 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 25 131 292 14 50 33 68 196 324), lower := (rows 25 131 292 14 50 33 64 128 256), losses := [] }

theorem u19162 : Upper (D 6) (R 6) [24,129,288,6,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19163 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 14 50 36 65 193 321), lower := (rows 25 131 292 14 50 36 64 128 256), losses := [] }

theorem u19163 : Upper (D 6) (R 6) [24,129,288,6,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19164 : Route 9 := (fun mask => (mask,id))

def c19164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19164 : Upper (D 6) (R 6) [24,129,288,6,34,64] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,34,64] 13 (by decide) (choices 1) [1,4] r19164 c19164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5702
  · exact u5703

def b19165 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 364, targets := 1 },{ cop := 5, region := 324, targets := 2 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 25 131 292 14 81 34 100 228 356), lower := (rows 25 131 292 14 81 34 64 128 256), losses := [] }

theorem u19165 : Upper (D 6) (R 6) [24,129,288,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19166 : PairBound 9 := { available := 98, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 14 81 36 98 226 354), lower := (rows 25 131 292 14 81 36 64 128 256), losses := [] }

theorem u19166 : Upper (D 6) (R 6) [24,129,288,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19167 : Route 9 := (fun mask => (mask,id))

def c19167 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19167 : Upper (D 6) (R 6) [24,129,288,6,65,64] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,65,64] 13 (by decide) (choices 1) [2,4,32] r19167 c19167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5704
  · exact u5705
  · exact u5706

def b19168 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 131 292 14 82 33 100 228 356), lower := (rows 25 131 292 14 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 24 32 100 164 292), good := (rows 24 130 484 478 82 484 64 128 256) }] }

theorem u19168 : Upper (D 6) (R 6) [24,129,288,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19169 : PairBound 9 := { available := 97, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 14 82 36 97 225 353), lower := (rows 25 131 292 14 82 36 64 128 256), losses := [] }

theorem u19169 : Upper (D 6) (R 6) [24,129,288,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19170 : Route 9 := (fun mask => (mask,id))

def c19170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19170 : Upper (D 6) (R 6) [24,129,288,6,66,64] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,66,64] 13 (by decide) (choices 1) [1,4,32] r19170 c19170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5707
  · exact u5708
  · exact u5709

def r19171 : Route 9 := (fun mask => (mask,id))

def c19171 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19171 : Upper (D 6) (R 6) [24,129,288,6,68,1] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,68,1] 13 (by decide) (choices 1) [2,32] r19171 c19171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5710
  · exact u5711

def r19172 : Route 9 := (fun mask => (mask,id))

def c19172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19172 : Upper (D 6) (R 6) [24,129,288,6,68,2] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,68,2] 13 (by decide) (choices 1) [1,32] r19172 c19172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5712
  · exact u5713

def r19173 : Route 9 := (fun mask => (mask,id))

def c19173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19173 : Upper (D 6) (R 6) [24,129,288,6,68,64] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,68,64] 13 (by decide) (choices 1) [1,2,32] r19173 c19173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5714
  · exact u5715
  · exact u5716

def r19174 : Route 9 := (fun mask => (mask,id))

def c19174 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19174 : Upper (D 6) (R 6) [24,129,288,6,96,1] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,96,1] 13 (by decide) (choices 1) [2,4] r19174 c19174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5717
  · exact u5718

def r19175 : Route 9 := (fun mask => (mask,id))

def c19175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19175 : Upper (D 6) (R 6) [24,129,288,6,96,2] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,96,2] 13 (by decide) (choices 1) [1,4] r19175 c19175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5719
  · exact u5720

def b19176 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 14 112 36 67 195 323), lower := (rows 25 131 292 14 112 36 64 128 256), losses := [] }

theorem u19176 : Upper (D 6) (R 6) [24,129,288,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19177 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 131 292 14 112 96 71 135 263), lower := (rows 25 131 292 14 112 96 64 128 256), losses := [] }

theorem u19177 : Upper (D 6) (R 6) [24,129,288,6,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19178 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 131 292 41 82 34 68 196 324), lower := (rows 25 131 292 41 82 34 64 128 256), losses := [] }

theorem u19178 : Upper (D 6) (R 6) [24,129,288,33,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19179 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 41 82 36 70 198 326), lower := (rows 25 131 292 41 82 36 64 128 256), losses := [] }

theorem u19179 : Upper (D 6) (R 6) [24,129,288,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19180 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 131 292 41 82 96 70 134 262), lower := (rows 25 131 292 41 82 96 64 128 256), losses := [] }

theorem u19180 : Upper (D 6) (R 6) [24,129,288,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19181 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 1, region := 40, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 131 292 41 84 34 70 198 326), lower := (rows 25 131 292 41 84 34 64 128 256), losses := [] }

theorem u19181 : Upper (D 6) (R 6) [24,129,288,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19182 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 131 292 41 84 36 66 194 322), lower := (rows 25 131 292 41 84 36 64 128 256), losses := [] }

theorem u19182 : Upper (D 6) (R 6) [24,129,288,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19183 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 131 292 41 84 96 70 134 262), lower := (rows 25 131 292 41 84 96 64 128 256), losses := [] }

theorem u19183 : Upper (D 6) (R 6) [24,129,288,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19184 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 25 131 292 42 81 34 68 196 324), lower := (rows 25 131 292 42 81 34 64 128 256), losses := [] }

theorem u19184 : Upper (D 6) (R 6) [24,129,288,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19185 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 42 81 36 70 198 326), lower := (rows 25 131 292 42 81 36 64 128 256), losses := [] }

theorem u19185 : Upper (D 6) (R 6) [24,129,288,34,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19186 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 364, targets := 1 },{ cop := 3, region := 260, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 25 131 292 42 81 96 70 134 262), lower := (rows 25 131 292 42 81 96 64 128 256), losses := [] }

theorem u19186 : Upper (D 6) (R 6) [24,129,288,34,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19187 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 131 292 42 82 33 68 196 324), lower := (rows 25 131 292 42 82 33 64 128 256), losses := [] }

theorem u19187 : Upper (D 6) (R 6) [24,129,288,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19188 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 42 82 36 69 197 325), lower := (rows 25 131 292 42 82 36 64 128 256), losses := [] }

theorem u19188 : Upper (D 6) (R 6) [24,129,288,34,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19189 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 25 131 292 42 82 96 69 133 261), lower := (rows 25 131 292 42 82 96 64 128 256), losses := [] }

theorem u19189 : Upper (D 6) (R 6) [24,129,288,34,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19190 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 40, targets := 68 },{ cop := 3, region := 324, targets := 1 }], pairs := [(2,0),(3,2),(3,6)], upper := (rows 25 131 292 42 84 33 70 198 326), lower := (rows 25 131 292 42 84 33 64 128 256), losses := [] }

theorem u19190 : Upper (D 6) (R 6) [24,129,288,34,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19191 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 131 292 42 84 34 69 197 325), lower := (rows 25 131 292 42 84 34 64 128 256), losses := [] }

theorem u19191 : Upper (D 6) (R 6) [24,129,288,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19192 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 42 84 36 67 195 323), lower := (rows 25 131 292 42 84 36 64 128 256), losses := [] }

theorem u19192 : Upper (D 6) (R 6) [24,129,288,34,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19193 : Route 9 := (fun mask => (mask,id))

def c19193 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19193 : Upper (D 6) (R 6) [24,129,288,34,68,64] 13 := by
  apply FastRouting.sound _ _ [24,129,288,34,68,64] 13 (by decide) (choices 1) [1,2,4] r19193 c19193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5721
  · exact u5722
  · exact u5723

def r19194 : Route 9 := (fun mask => (mask,id))

def c19194 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19194 : Upper (D 6) (R 6) [24,129,288,66,68,1] 13 := by
  apply FastRouting.sound _ _ [24,129,288,66,68,1] 13 (by decide) (choices 1) [2,4,32] r19194 c19194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5724
  · exact u5725
  · exact u5726

def r19195 : Route 9 := (fun mask => (mask,id))

def c19195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19195 : Upper (D 6) (R 6) [24,129,288,66,68,2] 13 := by
  apply FastRouting.sound _ _ [24,129,288,66,68,2] 13 (by decide) (choices 1) [1,4,32] r19195 c19195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5727
  · exact u5728
  · exact u5729

def b19196 : PairBound 9 := { available := 35, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 74 84 36 99 163 291), lower := (rows 25 131 292 74 84 36 64 128 256), losses := [] }

theorem u19196 : Upper (D 6) (R 6) [24,129,288,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19197 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 131 292 74 112 33 70 134 262), lower := (rows 25 131 292 74 112 33 64 128 256), losses := [] }

theorem u19197 : Upper (D 6) (R 6) [24,129,288,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19198 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(1,6),(2,6)], upper := (rows 25 131 292 74 112 34 69 133 261), lower := (rows 25 131 292 74 112 34 64 128 256), losses := [] }

theorem u19198 : Upper (D 6) (R 6) [24,129,288,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19199 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 74 112 36 71 135 263), lower := (rows 25 131 292 74 112 36 64 128 256), losses := [] }

theorem u19199 : Upper (D 6) (R 6) [24,129,288,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19199
end Delivery.IrregularNine14.P06
