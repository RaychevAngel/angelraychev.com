import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0095
import IrregularNine14P06C0096

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19200 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 131 292 76 112 33 70 134 262), lower := (rows 25 131 292 76 112 33 64 128 256), losses := [] }

theorem u19200 : Upper (D 6) (R 6) [24,129,288,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19201 : Route 9 := (fun mask => (mask,id))

def c19201 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19201 : Upper (D 6) (R 6) [24,129,288,68,96,2] 13 := by
  apply FastRouting.sound _ _ [24,129,288,68,96,2] 13 (by decide) (choices 1) [1,2,4] r19201 c19201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5730
  · exact u5731
  · exact u5732

def b19202 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 76 112 36 67 131 259), lower := (rows 25 131 292 76 112 36 64 128 256), losses := [] }

theorem u19202 : Upper (D 6) (R 6) [24,129,288,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19203 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 134 262 11 52 33 96 224 352), lower := (rows 25 134 262 11 52 33 64 128 256), losses := [] }

theorem u19203 : Upper (D 6) (R 6) [24,132,258,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19204 : Route 9 := (fun mask => (mask,id))

def c19204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19204 : Upper (D 6) (R 6) [24,132,258,3,36,64] 13 := by
  apply FastRouting.sound _ _ [24,132,258,3,36,64] 13 (by decide) (choices 1) [1,32] r19204 c19204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5733
  · exact u5734

def b19205 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 262 11 112 33 100 228 356), lower := (rows 25 134 262 11 112 33 64 128 256), losses := [] }

theorem u19205 : Upper (D 6) (R 6) [24,132,258,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19206_1 : Upper (D 6) (R 6) [24,132,258,3,96,4,1] 13 :=
  permutation_upper _ _ _ [24,132,258,3,96,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5735

def r19206 : Route 9 := (fun mask => (mask,id))

def c19206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19206 : Upper (D 6) (R 6) [24,132,258,3,96,4] 13 := by
  apply FastRouting.sound _ _ [24,132,258,3,96,4] 13 (by decide) (choices 1) [1,32] r19206 c19206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m19206_1
  · exact u5736

def b19207 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 134 262 11 112 96 101 165 293), lower := (rows 25 134 262 11 112 96 64 128 256), losses := [] }

theorem u19207 : Upper (D 6) (R 6) [24,132,258,3,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19208 : Route 9 := (fun mask => (mask,id))

def c19208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19208 : Upper (D 6) (R 6) [24,132,258,33,65,2] 13 := by
  apply FastRouting.sound _ _ [24,132,258,33,65,2] 13 (by decide) (choices 1) [4,32] r19208 c19208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5737
  · exact u5738

def b19209 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 25, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 134 262 41 81 96 102 166 294), lower := (rows 25 134 262 41 81 96 64 128 256), losses := [] }

theorem u19209 : Upper (D 6) (R 6) [24,132,258,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19210 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 134 262 41 82 33 100 228 356), lower := (rows 25 134 262 41 82 33 64 128 256), losses := [] }

theorem u19210 : Upper (D 6) (R 6) [24,132,258,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19211 : PairBound 9 := { available := 97, camps := [], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 134 262 41 82 36 97 225 353), lower := (rows 25 134 262 41 82 36 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 24 16 38 88 152 280), good := (rows 473 164 292 489 505 36 64 128 256) },{ target := 6, region := (rows 17 2 4 24 16 38 0 128 256), good := (rows 25 166 294 41 59 36 0 128 256) }] }

theorem u19211 : Upper (D 6) (R 6) [24,132,258,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19212 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 134 262 41 82 96 101 165 293), lower := (rows 25 134 262 41 82 96 64 128 256), losses := [] }

theorem u19212 : Upper (D 6) (R 6) [24,132,258,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19213 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 134 262 42 52 33 65 193 321), lower := (rows 25 134 262 42 52 33 64 128 256), losses := [] }

theorem u19213 : Upper (D 6) (R 6) [24,132,258,34,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19214 : Route 9 := (fun mask => (mask,id))

def c19214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19214 : Upper (D 6) (R 6) [24,132,258,34,36,64] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,36,64] 13 (by decide) (choices 1) [1] r19214 c19214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u5739

def r19215 : Route 9 := (fun mask => (mask,id))

def c19215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19215 : Upper (D 6) (R 6) [24,132,258,34,68,1] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,68,1] 13 (by decide) (choices 1) [1,32] r19215 c19215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5740
  · exact u5741

theorem m19216_1 : Upper (D 6) (R 6) [24,132,258,34,68,64,1] 13 :=
  permutation_upper _ _ _ [24,132,258,34,68,1,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5741

def r19216 : Route 9 := (fun mask => (mask,id))

def c19216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19216 : Upper (D 6) (R 6) [24,132,258,34,68,64] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,68,64] 13 (by decide) (choices 1) [1,32] r19216 c19216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m19216_1
  · exact u5742

def r19217 : Route 9 := (fun mask => (mask,id))

def c19217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19217 : Upper (D 6) (R 6) [24,132,258,34,96,1] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,96,1] 13 (by decide) (choices 1) [1,4] r19217 c19217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5743
  · exact u5744

def b19218 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 81, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 134 262 42 112 36 65 193 321), lower := (rows 25 134 262 42 112 36 64 128 256), losses := [] }

theorem u19218 : Upper (D 6) (R 6) [24,132,258,34,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19219 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 134 262 42 112 96 69 133 261), lower := (rows 25 134 262 42 112 96 64 128 256), losses := [] }

theorem u19219 : Upper (D 6) (R 6) [24,132,258,34,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19220 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 324, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 134 292 11 81 34 100 228 356), lower := (rows 25 134 292 11 81 34 64 128 256), losses := [] }

theorem u19220 : Upper (D 6) (R 6) [24,132,288,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19221 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 8, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 134 292 11 81 36 98 226 354), lower := (rows 25 134 292 11 81 36 64 128 256), losses := [] }

theorem u19221 : Upper (D 6) (R 6) [24,132,288,3,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19222 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 390, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 134 292 11 81 96 102 166 294), lower := (rows 25 134 292 11 81 96 64 128 256), losses := [] }

theorem u19222 : Upper (D 6) (R 6) [24,132,288,3,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19223 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 292 11 84 33 98 226 354), lower := (rows 25 134 292 11 84 33 64 128 256), losses := [] }

theorem u19223 : Upper (D 6) (R 6) [24,132,288,3,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19224 : Route 9 := (fun mask => (mask,id))

def c19224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19224 : Upper (D 6) (R 6) [24,132,288,3,68,2] 13 := by
  apply FastRouting.sound _ _ [24,132,288,3,68,2] 13 (by decide) (choices 1) [1,32] r19224 c19224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5745
  · exact u5746

def r19225 : Route 9 := (fun mask => (mask,id))

def c19225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19225 : Upper (D 6) (R 6) [24,132,288,3,68,64] 13 := by
  apply FastRouting.sound _ _ [24,132,288,3,68,64] 13 (by decide) (choices 1) [1,2,32] r19225 c19225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5747
  · exact u5748
  · exact u5749

def b19226 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 292 11 112 33 70 198 326), lower := (rows 25 134 292 11 112 33 64 128 256), losses := [] }

theorem u19226 : Upper (D 6) (R 6) [24,132,288,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19227 : Route 9 := (fun mask => (mask,id))

def c19227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19227 : Upper (D 6) (R 6) [24,132,288,3,96,2] 13 := by
  apply FastRouting.sound _ _ [24,132,288,3,96,2] 13 (by decide) (choices 1) [1,4] r19227 c19227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5750
  · exact u5751

def b19228 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 134 292 11 112 36 67 195 323), lower := (rows 25 134 292 11 112 36 64 128 256), losses := [] }

theorem u19228 : Upper (D 6) (R 6) [24,132,288,3,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19229 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 134 292 11 112 96 71 135 263), lower := (rows 25 134 292 11 112 96 64 128 256), losses := [] }

theorem u19229 : Upper (D 6) (R 6) [24,132,288,3,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19230 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 134 292 13 50 33 66 194 322), lower := (rows 25 134 292 13 50 33 64 128 256), losses := [] }

theorem u19230 : Upper (D 6) (R 6) [24,132,288,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19231 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 134 292 13 50 34 65 193 321), lower := (rows 25 134 292 13 50 34 64 128 256), losses := [] }

theorem u19231 : Upper (D 6) (R 6) [24,132,288,5,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19232 : Route 9 := (fun mask => (mask,id))

def c19232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19232 : Upper (D 6) (R 6) [24,132,288,5,34,64] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,34,64] 13 (by decide) (choices 1) [1,2] r19232 c19232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5752
  · exact u5753

def r19233 : Route 9 := (fun mask => (mask,id))

def c19233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19233 : Upper (D 6) (R 6) [24,132,288,5,65,2] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,65,2] 13 (by decide) (choices 1) [2,32] r19233 c19233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5754
  · exact u5755

def b19234 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 390, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 134 292 13 81 96 98 162 290), lower := (rows 25 134 292 13 81 96 64 128 256), losses := [] }

theorem u19234 : Upper (D 6) (R 6) [24,132,288,5,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19235 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 292 13 82 33 98 226 354), lower := (rows 25 134 292 13 82 33 64 128 256), losses := [] }

theorem u19235 : Upper (D 6) (R 6) [24,132,288,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19236 : Route 9 := (fun mask => (mask,id))

def c19236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19236 : Upper (D 6) (R 6) [24,132,288,5,66,2] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,66,2] 13 (by decide) (choices 1) [1,32] r19236 c19236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5756
  · exact u5757

def r19237 : Route 9 := (fun mask => (mask,id))

def c19237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19237 : Upper (D 6) (R 6) [24,132,288,5,66,64] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,66,64] 13 (by decide) (choices 1) [1,2,32] r19237 c19237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5758
  · exact u5759
  · exact u5760

def b19238 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 292 13 112 33 66 194 322), lower := (rows 25 134 292 13 112 33 64 128 256), losses := [] }

theorem u19238 : Upper (D 6) (R 6) [24,132,288,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19239 : Route 9 := (fun mask => (mask,id))

def c19239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19239 : Upper (D 6) (R 6) [24,132,288,5,96,2] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,96,2] 13 (by decide) (choices 1) [1,2] r19239 c19239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5761
  · exact u5762

def b19240 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 134 292 13 112 96 67 131 259), lower := (rows 25 134 292 13 112 96 64 128 256), losses := [] }

theorem u19240 : Upper (D 6) (R 6) [24,132,288,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19241 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 134 292 41 82 33 70 198 326), lower := (rows 25 134 292 41 82 33 64 128 256), losses := [] }

theorem u19241 : Upper (D 6) (R 6) [24,132,288,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19242 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 134 292 41 82 34 69 197 325), lower := (rows 25 134 292 41 82 34 64 128 256), losses := [] }

theorem u19242 : Upper (D 6) (R 6) [24,132,288,33,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19243 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 134 292 41 82 36 67 195 323), lower := (rows 25 134 292 41 82 36 64 128 256), losses := [] }

theorem u19243 : Upper (D 6) (R 6) [24,132,288,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19244 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 134 292 41 82 96 71 135 263), lower := (rows 25 134 292 41 82 96 64 128 256), losses := [] }

theorem u19244 : Upper (D 6) (R 6) [24,132,288,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19245 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 134 292 41 84 33 66 194 322), lower := (rows 25 134 292 41 84 33 64 128 256), losses := [] }

theorem u19245 : Upper (D 6) (R 6) [24,132,288,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19246 : Route 9 := (fun mask => (mask,id))

def c19246 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19246 : Upper (D 6) (R 6) [24,132,288,33,68,2] 13 := by
  apply FastRouting.sound _ _ [24,132,288,33,68,2] 13 (by decide) (choices 1) [1,2] r19246 c19246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5763
  · exact u5764

def b19247 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 134 292 41 84 96 67 131 259), lower := (rows 25 134 292 41 84 96 64 128 256), losses := [] }

theorem u19247 : Upper (D 6) (R 6) [24,132,288,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19248 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 134 292 42 81 33 70 198 326), lower := (rows 25 134 292 42 81 33 64 128 256), losses := [] }

theorem u19248 : Upper (D 6) (R 6) [24,132,288,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19249 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 134 292 42 81 34 69 197 325), lower := (rows 25 134 292 42 81 34 64 128 256), losses := [] }

theorem u19249 : Upper (D 6) (R 6) [24,132,288,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19250 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 81, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 134 292 42 81 36 67 195 323), lower := (rows 25 134 292 42 81 36 64 128 256), losses := [] }

theorem u19250 : Upper (D 6) (R 6) [24,132,288,34,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19251 : Route 9 := (fun mask => (mask,id))

def c19251 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19251 : Upper (D 6) (R 6) [24,132,288,34,65,64] 13 := by
  apply FastRouting.sound _ _ [24,132,288,34,65,64] 13 (by decide) (choices 1) [1,2,4] r19251 c19251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5765
  · exact u5766
  · exact u5767

def b19252 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 134 292 42 82 33 69 197 325), lower := (rows 25 134 292 42 82 33 64 128 256), losses := [] }

theorem u19252 : Upper (D 6) (R 6) [24,132,288,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19253 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 81, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 134 292 42 82 36 65 193 321), lower := (rows 25 134 292 42 82 36 64 128 256), losses := [] }

theorem u19253 : Upper (D 6) (R 6) [24,132,288,34,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19254 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 25 134 292 42 82 96 69 133 261), lower := (rows 25 134 292 42 82 96 64 128 256), losses := [] }

theorem u19254 : Upper (D 6) (R 6) [24,132,288,34,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19255 : Route 9 := (fun mask => (mask,id))

def c19255 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19255 : Upper (D 6) (R 6) [24,132,288,34,68,1] 13 := by
  apply FastRouting.sound _ _ [24,132,288,34,68,1] 13 (by decide) (choices 1) [1,2] r19255 c19255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5768
  · exact u5769

def b19256 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 134 292 42 84 34 65 193 321), lower := (rows 25 134 292 42 84 34 64 128 256), losses := [] }

theorem u19256 : Upper (D 6) (R 6) [24,132,288,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19257 : Route 9 := (fun mask => (mask,id))

def c19257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19257 : Upper (D 6) (R 6) [24,132,288,34,68,64] 13 := by
  apply FastRouting.sound _ _ [24,132,288,34,68,64] 13 (by decide) (choices 1) [1,2] r19257 c19257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5770
  · exact u5771

def r19258 : Route 9 := (fun mask => (mask,id))

def c19258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19258 : Upper (D 6) (R 6) [24,132,288,66,68,1] 13 := by
  apply FastRouting.sound _ _ [24,132,288,66,68,1] 13 (by decide) (choices 1) [1,2,32] r19258 c19258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5772
  · exact u5773
  · exact u5774

def r19259 : Route 9 := (fun mask => (mask,id))

def c19259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19259 : Upper (D 6) (R 6) [24,132,288,66,68,2] 13 := by
  apply FastRouting.sound _ _ [24,132,288,66,68,2] 13 (by decide) (choices 1) [1,32] r19259 c19259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5775
  · exact u5776

#print axioms u19259
end Delivery.IrregularNine14.P06
