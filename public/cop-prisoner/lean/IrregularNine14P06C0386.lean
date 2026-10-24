import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0118

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23160 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 25 276 96 75 139 267), lower := (rows 35 134 100 25 276 96 64 128 256), losses := [] }

theorem u23160 : Upper (D 6) (R 6) [34,132,96,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23161 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 100 25 280 33 70 198 326), lower := (rows 35 134 100 25 280 33 64 128 256), losses := [] }

theorem u23161 : Upper (D 6) (R 6) [34,132,96,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23162 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 25 280 34 69 197 325), lower := (rows 35 134 100 25 280 34 64 128 256), losses := [] }

theorem u23162 : Upper (D 6) (R 6) [34,132,96,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23163 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 25 280 36 67 195 323), lower := (rows 35 134 100 25 280 36 64 128 256), losses := [] }

theorem u23163 : Upper (D 6) (R 6) [34,132,96,17,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23164 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 25 280 96 71 135 263), lower := (rows 35 134 100 25 280 96 64 128 256), losses := [] }

theorem u23164 : Upper (D 6) (R 6) [34,132,96,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23165 : Route 9 := (fun mask => (mask,id))

def c23165 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23165 : Upper (D 6) (R 6) [34,132,96,17,320,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,17,320,1] 13 (by decide) (choices 1) [2,4,8] r23165 c23165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7096
  · exact u7097
  · exact u7098

def b23166 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 25 336 34 77 141 269), lower := (rows 35 134 100 25 336 34 64 128 256), losses := [] }

theorem u23166 : Upper (D 6) (R 6) [34,132,96,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23167 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 25 336 36 75 139 267), lower := (rows 35 134 100 25 336 36 64 128 256), losses := [] }

theorem u23167 : Upper (D 6) (R 6) [34,132,96,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23168 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 25 336 40 71 135 263), lower := (rows 35 134 100 25 336 40 64 128 256), losses := [] }

theorem u23168 : Upper (D 6) (R 6) [34,132,96,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23168 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23169 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 36, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 100 26 81 33 332 396 268), lower := (rows 35 134 100 26 81 33 64 128 256), losses := [] }

theorem u23169 : Upper (D 6) (R 6) [34,132,96,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23170 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 26 81 36 329 393 265), lower := (rows 35 134 100 26 81 36 64 128 256), losses := [] }

theorem u23170 : Upper (D 6) (R 6) [34,132,96,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23171 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 100 26 81 40 325 389 261), lower := (rows 35 134 100 26 81 40 64 128 256), losses := [] }

theorem u23171 : Upper (D 6) (R 6) [34,132,96,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23171 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23172 : Route 9 := (fun mask => (mask,id))

def c23172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23172 : Upper (D 6) (R 6) [34,132,96,18,65,256] 13 := by
  apply FastRouting.sound _ _ [34,132,96,18,65,256] 13 (by decide) (choices 1) [1,4,8] r23172 c23172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7099
  · exact u7100
  · exact u7101

def b23173 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 100 26 273 33 76 204 332), lower := (rows 35 134 100 26 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 33 132 100 508 305 33 64 128 256) }] }

theorem u23173 : Upper (D 6) (R 6) [34,132,96,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23174 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 26 273 36 73 201 329), lower := (rows 35 134 100 26 273 36 64 128 256), losses := [] }

theorem u23174 : Upper (D 6) (R 6) [34,132,96,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23175 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 100 26 273 40 69 197 325), lower := (rows 35 134 100 26 273 40 64 128 256), losses := [] }

theorem u23175 : Upper (D 6) (R 6) [34,132,96,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23175 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23176 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 26 273 96 77 141 269), lower := (rows 35 134 100 26 273 96 64 128 256), losses := [] }

theorem u23176 : Upper (D 6) (R 6) [34,132,96,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23177 : Route 9 := (fun mask => (mask,id))

def c23177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23177 : Upper (D 6) (R 6) [34,132,96,18,260,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,18,260,1] 13 (by decide) (choices 1) [1,8] r23177 c23177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7102
  · exact u7103

def b23178 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 100 26 276 40 65 193 321), lower := (rows 35 134 100 26 276 40 64 128 256), losses := [] }

theorem u23178 : Upper (D 6) (R 6) [34,132,96,18,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23178 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23179 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 26 276 96 73 137 265), lower := (rows 35 134 100 26 276 96 64 128 256), losses := [] }

theorem u23179 : Upper (D 6) (R 6) [34,132,96,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23180 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 100 26 280 33 69 197 325), lower := (rows 35 134 100 26 280 33 64 128 256), losses := [] }

theorem u23180 : Upper (D 6) (R 6) [34,132,96,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23181 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 26 280 36 65 193 321), lower := (rows 35 134 100 26 280 36 64 128 256), losses := [] }

theorem u23181 : Upper (D 6) (R 6) [34,132,96,18,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23182 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 26 280 96 69 133 261), lower := (rows 35 134 100 26 280 96 64 128 256), losses := [] }

theorem u23182 : Upper (D 6) (R 6) [34,132,96,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23183 : Route 9 := (fun mask => (mask,id))

def c23183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23183 : Upper (D 6) (R 6) [34,132,96,18,320,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,18,320,1] 13 (by decide) (choices 1) [1,4,8] r23183 c23183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7104
  · exact u7105
  · exact u7106

def b23184 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 26 336 36 73 137 265), lower := (rows 35 134 100 26 336 36 64 128 256), losses := [] }

theorem u23184 : Upper (D 6) (R 6) [34,132,96,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23185 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 100 26 336 40 69 133 261), lower := (rows 35 134 100 26 336 40 64 128 256), losses := [] }

theorem u23185 : Upper (D 6) (R 6) [34,132,96,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23185 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23186 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 386, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 100 28 81 33 330 394 266), lower := (rows 35 134 100 28 81 33 64 128 256), losses := [] }

theorem u23186 : Upper (D 6) (R 6) [34,132,96,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23187 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 28 81 34 329 393 265), lower := (rows 35 134 100 28 81 34 64 128 256), losses := [] }

theorem u23187 : Upper (D 6) (R 6) [34,132,96,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23188 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 134 100 28 81 40 323 387 259), lower := (rows 35 134 100 28 81 40 64 128 256), losses := [] }

theorem u23188 : Upper (D 6) (R 6) [34,132,96,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23188 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23189 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 28 81 288 75 139 267), lower := (rows 35 134 100 28 81 288 64 128 256), losses := [] }

theorem u23189 : Upper (D 6) (R 6) [34,132,96,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23189 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23190 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 419, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 100 28 82 33 329 393 265), lower := (rows 35 134 100 28 82 33 64 128 256), losses := [] }

theorem u23190 : Upper (D 6) (R 6) [34,132,96,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23191 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 134 100 28 82 40 321 385 257), lower := (rows 35 134 100 28 82 40 64 128 256), losses := [] }

theorem u23191 : Upper (D 6) (R 6) [34,132,96,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23191 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23192 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 28 82 288 73 137 265), lower := (rows 35 134 100 28 82 288 64 128 256), losses := [] }

theorem u23192 : Upper (D 6) (R 6) [34,132,96,20,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23192 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23193 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 100 28 273 33 74 202 330), lower := (rows 35 134 100 28 273 33 64 128 256), losses := [] }

theorem u23193 : Upper (D 6) (R 6) [34,132,96,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23194 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 28 273 34 73 201 329), lower := (rows 35 134 100 28 273 34 64 128 256), losses := [] }

theorem u23194 : Upper (D 6) (R 6) [34,132,96,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23195 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 100 28 273 40 67 195 323), lower := (rows 35 134 100 28 273 40 64 128 256), losses := [] }

theorem u23195 : Upper (D 6) (R 6) [34,132,96,20,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23195 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23196 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 28 273 96 75 139 267), lower := (rows 35 134 100 28 273 96 64 128 256), losses := [] }

theorem u23196 : Upper (D 6) (R 6) [34,132,96,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23197 : Route 9 := (fun mask => (mask,id))

def c23197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23197 : Upper (D 6) (R 6) [34,132,96,20,258,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,20,258,1] 13 (by decide) (choices 1) [1,8] r23197 c23197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7107
  · exact u7108

def b23198 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 100 28 274 40 65 193 321), lower := (rows 35 134 100 28 274 40 64 128 256), losses := [] }

theorem u23198 : Upper (D 6) (R 6) [34,132,96,20,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23198 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23199 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 28 274 96 73 137 265), lower := (rows 35 134 100 28 274 96 64 128 256), losses := [] }

theorem u23199 : Upper (D 6) (R 6) [34,132,96,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23200 : Route 9 := (fun mask => (mask,id))

def c23200 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23200 : Upper (D 6) (R 6) [34,132,96,20,264,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,20,264,1] 13 (by decide) (choices 1) [1,2] r23200 c23200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7109
  · exact u7110

def b23201 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 28 280 34 65 193 321), lower := (rows 35 134 100 28 280 34 64 128 256), losses := [] }

theorem u23201 : Upper (D 6) (R 6) [34,132,96,20,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23202 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 100 28 280 96 67 131 259), lower := (rows 35 134 100 28 280 96 64 128 256), losses := [] }

theorem u23202 : Upper (D 6) (R 6) [34,132,96,20,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23203 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 100 28 336 33 75 139 267), lower := (rows 35 134 100 28 336 33 64 128 256), losses := [] }

theorem u23203 : Upper (D 6) (R 6) [34,132,96,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23204 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 28 336 34 73 137 265), lower := (rows 35 134 100 28 336 34 64 128 256), losses := [] }

theorem u23204 : Upper (D 6) (R 6) [34,132,96,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23205 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 134 100 28 336 40 67 131 259), lower := (rows 35 134 100 28 336 40 64 128 256), losses := [] }

theorem u23205 : Upper (D 6) (R 6) [34,132,96,20,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23205 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23206 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 73 273 34 92 156 284), lower := (rows 35 134 100 73 273 34 64 128 256), losses := [] }

theorem u23206 : Upper (D 6) (R 6) [34,132,96,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23207 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 73 273 36 90 154 282), lower := (rows 35 134 100 73 273 36 64 128 256), losses := [] }

theorem u23207 : Upper (D 6) (R 6) [34,132,96,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23208 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 73 273 40 86 150 278), lower := (rows 35 134 100 73 273 40 64 128 256), losses := [] }

theorem u23208 : Upper (D 6) (R 6) [34,132,96,65,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23208 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23209 : Route 9 := (fun mask => (mask,id))

def c23209 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23209 : Upper (D 6) (R 6) [34,132,96,65,257,16] 13 := by
  apply FastRouting.sound _ _ [34,132,96,65,257,16] 13 (by decide) (choices 1) [2,4,8] r23209 c23209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7111
  · exact u7112
  · exact u7113

def b23210 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 36, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 100 73 274 33 92 156 284), lower := (rows 35 134 100 73 274 33 64 128 256), losses := [] }

theorem u23210 : Upper (D 6) (R 6) [34,132,96,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23211 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 73 274 36 89 153 281), lower := (rows 35 134 100 73 274 36 64 128 256), losses := [] }

theorem u23211 : Upper (D 6) (R 6) [34,132,96,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23212 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 73 274 40 85 149 277), lower := (rows 35 134 100 73 274 40 64 128 256), losses := [] }

theorem u23212 : Upper (D 6) (R 6) [34,132,96,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23212 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23213 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 100 73 274 48 77 141 269), lower := (rows 35 134 100 73 274 48 64 128 256), losses := [] }

theorem u23213 : Upper (D 6) (R 6) [34,132,96,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23213 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23214 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 36, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 100 73 276 33 90 154 282), lower := (rows 35 134 100 73 276 33 64 128 256), losses := [] }

theorem u23214 : Upper (D 6) (R 6) [34,132,96,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23215 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 73 276 34 89 153 281), lower := (rows 35 134 100 73 276 34 64 128 256), losses := [] }

theorem u23215 : Upper (D 6) (R 6) [34,132,96,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23216 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 73 276 40 83 147 275), lower := (rows 35 134 100 73 276 40 64 128 256), losses := [] }

theorem u23216 : Upper (D 6) (R 6) [34,132,96,65,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23216 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23217 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 100 73 276 48 75 139 267), lower := (rows 35 134 100 73 276 48 64 128 256), losses := [] }

theorem u23217 : Upper (D 6) (R 6) [34,132,96,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23217 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23218 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 36, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 100 73 280 33 86 150 278), lower := (rows 35 134 100 73 280 33 64 128 256), losses := [] }

theorem u23218 : Upper (D 6) (R 6) [34,132,96,65,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23219 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 73 280 34 85 149 277), lower := (rows 35 134 100 73 280 34 64 128 256), losses := [] }

theorem u23219 : Upper (D 6) (R 6) [34,132,96,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23219
end Delivery.IrregularNine14.P06
