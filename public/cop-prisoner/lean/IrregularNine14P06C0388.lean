import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0119

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23280 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 261 28 82 33 104 232 360), lower := (rows 35 134 261 28 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 21 32 65 129 257), good := (rows 506 158 478 30 90 496 64 128 256) }] }

theorem u23280 : Upper (D 6) (R 6) [34,132,257,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23281 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,2)], upper := (rows 35 134 261 28 82 40 97 225 353), lower := (rows 35 134 261 28 82 40 64 128 256), losses := [] }

theorem u23281 : Upper (D 6) (R 6) [34,132,257,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23281 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23282 : Route 9 := (fun mask => (mask,id))

def c23282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23282 : Upper (D 6) (R 6) [34,132,257,20,66,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,20,66,64] 13 (by decide) (choices 1) [1,8,32] r23282 c23282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7148
  · exact u7149
  · exact u7150

def b23283 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 261 28 88 33 98 226 354), lower := (rows 35 134 261 28 88 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 21 32 65 129 257), good := (rows 506 158 478 30 88 496 64 128 256) }] }

theorem u23283 : Upper (D 6) (R 6) [34,132,257,20,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23284 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 28 88 34 97 225 353), lower := (rows 35 134 261 28 88 34 64 128 256), losses := [] }

theorem u23284 : Upper (D 6) (R 6) [34,132,257,20,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23285 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 261 28 88 96 99 163 291), lower := (rows 35 134 261 28 88 96 64 128 256), losses := [] }

theorem u23285 : Upper (D 6) (R 6) [34,132,257,20,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23286 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 261 28 112 33 74 202 330), lower := (rows 35 134 261 28 112 33 64 128 256), losses := [] }

theorem u23286 : Upper (D 6) (R 6) [34,132,257,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23287 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 28 112 34 73 201 329), lower := (rows 35 134 261 28 112 34 64 128 256), losses := [] }

theorem u23287 : Upper (D 6) (R 6) [34,132,257,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23288 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 28 112 40 67 195 323), lower := (rows 35 134 261 28 112 40 64 128 256), losses := [] }

theorem u23288 : Upper (D 6) (R 6) [34,132,257,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23288 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23289 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 261 28 112 96 75 139 267), lower := (rows 35 134 261 28 112 96 64 128 256), losses := [] }

theorem u23289 : Upper (D 6) (R 6) [34,132,257,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23290 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 44 81 34 88 216 344), lower := (rows 35 134 261 44 81 34 64 128 256), losses := [] }

theorem u23290 : Upper (D 6) (R 6) [34,132,257,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23291 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 44 81 40 82 210 338), lower := (rows 35 134 261 44 81 40 64 128 256), losses := [] }

theorem u23291 : Upper (D 6) (R 6) [34,132,257,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23291 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23292 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 194, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 261 44 81 48 74 202 330), lower := (rows 35 134 261 44 81 48 64 128 256), losses := [] }

theorem u23292 : Upper (D 6) (R 6) [34,132,257,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23292 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23293 : Route 9 := (fun mask => (mask,id))

def c23293 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23293 : Upper (D 6) (R 6) [34,132,257,36,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,36,65,64] 13 (by decide) (choices 1) [2,8,16] r23293 c23293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7151
  · exact u7152
  · exact u7153

def b23294 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 261 44 82 33 88 216 344), lower := (rows 35 134 261 44 82 33 64 128 256), losses := [] }

theorem u23294 : Upper (D 6) (R 6) [34,132,257,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23295 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 44 82 40 81 209 337), lower := (rows 35 134 261 44 82 40 64 128 256), losses := [] }

theorem u23295 : Upper (D 6) (R 6) [34,132,257,36,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23295 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23296 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 261 44 82 48 73 201 329), lower := (rows 35 134 261 44 82 48 64 128 256), losses := [] }

theorem u23296 : Upper (D 6) (R 6) [34,132,257,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23296 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23297 : Route 9 := (fun mask => (mask,id))

def c23297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23297 : Upper (D 6) (R 6) [34,132,257,36,66,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,36,66,64] 13 (by decide) (choices 1) [1,8,16] r23297 c23297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7154
  · exact u7155
  · exact u7156

def b23298 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 261 44 88 33 82 210 338), lower := (rows 35 134 261 44 88 33 64 128 256), losses := [] }

theorem u23298 : Upper (D 6) (R 6) [34,132,257,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23299 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 44 88 34 81 209 337), lower := (rows 35 134 261 44 88 34 64 128 256), losses := [] }

theorem u23299 : Upper (D 6) (R 6) [34,132,257,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23300 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 44 88 48 67 195 323), lower := (rows 35 134 261 44 88 48 64 128 256), losses := [] }

theorem u23300 : Upper (D 6) (R 6) [34,132,257,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23300 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23301 : Route 9 := (fun mask => (mask,id))

def c23301 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23301 : Upper (D 6) (R 6) [34,132,257,36,72,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,36,72,64] 13 (by decide) (choices 1) [1,2,16] r23301 c23301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7157
  · exact u7158
  · exact u7159

def b23302 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 56 81 34 76 204 332), lower := (rows 35 134 261 56 81 34 64 128 256), losses := [] }

theorem u23302 : Upper (D 6) (R 6) [34,132,257,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23303 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 261 56 81 36 74 202 330), lower := (rows 35 134 261 56 81 36 64 128 256), losses := [] }

theorem u23303 : Upper (D 6) (R 6) [34,132,257,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23304 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 261 56 81 40 70 198 326), lower := (rows 35 134 261 56 81 40 64 128 256), losses := [] }

theorem u23304 : Upper (D 6) (R 6) [34,132,257,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23304 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23305 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 261 56 81 96 78 142 270), lower := (rows 35 134 261 56 81 96 64 128 256), losses := [] }

theorem u23305 : Upper (D 6) (R 6) [34,132,257,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23306 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 261 56 82 33 76 204 332), lower := (rows 35 134 261 56 82 33 64 128 256), losses := [] }

theorem u23306 : Upper (D 6) (R 6) [34,132,257,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23307 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 261 56 82 36 73 201 329), lower := (rows 35 134 261 56 82 36 64 128 256), losses := [] }

theorem u23307 : Upper (D 6) (R 6) [34,132,257,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23308 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 261 56 82 40 69 197 325), lower := (rows 35 134 261 56 82 40 64 128 256), losses := [] }

theorem u23308 : Upper (D 6) (R 6) [34,132,257,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23308 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23309 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 261 56 82 96 77 141 269), lower := (rows 35 134 261 56 82 96 64 128 256), losses := [] }

theorem u23309 : Upper (D 6) (R 6) [34,132,257,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23310 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 261 56 84 33 74 202 330), lower := (rows 35 134 261 56 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 22 4 9 22 32 77 141 269), good := (rows 506 470 478 506 470 488 64 128 256) }] }

theorem u23310 : Upper (D 6) (R 6) [34,132,257,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23311 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 56 84 34 73 201 329), lower := (rows 35 134 261 56 84 34 64 128 256), losses := [] }

theorem u23311 : Upper (D 6) (R 6) [34,132,257,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23312 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 261 56 84 40 67 195 323), lower := (rows 35 134 261 56 84 40 64 128 256), losses := [] }

theorem u23312 : Upper (D 6) (R 6) [34,132,257,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23312 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23313 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 261 56 84 96 75 139 267), lower := (rows 35 134 261 56 84 96 64 128 256), losses := [] }

theorem u23313 : Upper (D 6) (R 6) [34,132,257,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23314 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 134 261 56 88 33 70 198 326), lower := (rows 35 134 261 56 88 33 64 128 256), losses := [] }

theorem u23314 : Upper (D 6) (R 6) [34,132,257,48,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23315 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 56 88 34 69 197 325), lower := (rows 35 134 261 56 88 34 64 128 256), losses := [] }

theorem u23315 : Upper (D 6) (R 6) [34,132,257,48,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23316 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 134 261 56 88 36 67 195 323), lower := (rows 35 134 261 56 88 36 64 128 256), losses := [] }

theorem u23316 : Upper (D 6) (R 6) [34,132,257,48,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23317 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 261 56 88 96 71 135 263), lower := (rows 35 134 261 56 88 96 64 128 256), losses := [] }

theorem u23317 : Upper (D 6) (R 6) [34,132,257,48,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23318 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 261 73 82 36 120 184 312), lower := (rows 35 134 261 73 82 36 64 128 256), losses := [] }

theorem u23318 : Upper (D 6) (R 6) [34,132,257,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23319 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 134 261 73 82 40 116 180 308), lower := (rows 35 134 261 73 82 40 64 128 256), losses := [] }

theorem u23319 : Upper (D 6) (R 6) [34,132,257,65,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23319 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23320 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 261 73 82 48 108 172 300), lower := (rows 35 134 261 73 82 48 64 128 256), losses := [] }

theorem u23320 : Upper (D 6) (R 6) [34,132,257,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23320 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23321 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 73 84 34 120 184 312), lower := (rows 35 134 261 73 84 34 64 128 256), losses := [] }

theorem u23321 : Upper (D 6) (R 6) [34,132,257,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23322 : Route 9 := (fun mask => (mask,id))

def c23322 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23322 : Upper (D 6) (R 6) [34,132,257,65,68,8] 13 := by
  apply FastRouting.sound _ _ [34,132,257,65,68,8] 13 (by decide) (choices 1) [2,16,32] r23322 c23322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7160
  · exact u7161
  · exact u7162

def r23323 : Route 9 := (fun mask => (mask,id))

def c23323 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23323 : Upper (D 6) (R 6) [34,132,257,65,68,16] 13 := by
  apply FastRouting.sound _ _ [34,132,257,65,68,16] 13 (by decide) (choices 1) [2,8,32] r23323 c23323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7163
  · exact u7164
  · exact u7165

def b23324 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 73 112 34 92 156 284), lower := (rows 35 134 261 73 112 34 64 128 256), losses := [] }

theorem u23324 : Upper (D 6) (R 6) [34,132,257,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23325 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 261 73 112 36 90 154 282), lower := (rows 35 134 261 73 112 36 64 128 256), losses := [] }

theorem u23325 : Upper (D 6) (R 6) [34,132,257,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23326 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 134 261 73 112 40 86 150 278), lower := (rows 35 134 261 73 112 40 64 128 256), losses := [] }

theorem u23326 : Upper (D 6) (R 6) [34,132,257,65,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23326 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23327 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 73 112 48 78 142 270), lower := (rows 35 134 261 73 112 48 64 128 256), losses := [] }

theorem u23327 : Upper (D 6) (R 6) [34,132,257,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23327 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23328 : Route 9 := (fun mask => (mask,id))

def c23328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23328 : Upper (D 6) (R 6) [34,132,257,66,68,1] 13 := by
  apply FastRouting.sound _ _ [34,132,257,66,68,1] 13 (by decide) (choices 1) [8,16,32] r23328 c23328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7166
  · exact u7167
  · exact u7168

def b23329 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 261 74 84 40 113 177 305), lower := (rows 35 134 261 74 84 40 64 128 256), losses := [] }

theorem u23329 : Upper (D 6) (R 6) [34,132,257,66,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23329 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23330 : Route 9 := (fun mask => (mask,id))

def c23330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23330 : Upper (D 6) (R 6) [34,132,257,66,68,16] 13 := by
  apply FastRouting.sound _ _ [34,132,257,66,68,16] 13 (by decide) (choices 1) [1,8,32] r23330 c23330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7169
  · exact u7170
  · exact u7171

def b23331 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 261 74 112 33 92 156 284), lower := (rows 35 134 261 74 112 33 64 128 256), losses := [] }

theorem u23331 : Upper (D 6) (R 6) [34,132,257,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23332 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 261 74 112 36 89 153 281), lower := (rows 35 134 261 74 112 36 64 128 256), losses := [] }

theorem u23332 : Upper (D 6) (R 6) [34,132,257,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23333 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 261 74 112 40 85 149 277), lower := (rows 35 134 261 74 112 40 64 128 256), losses := [] }

theorem u23333 : Upper (D 6) (R 6) [34,132,257,66,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23333 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23334 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 74 112 48 77 141 269), lower := (rows 35 134 261 74 112 48 64 128 256), losses := [] }

theorem u23334 : Upper (D 6) (R 6) [34,132,257,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23334 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23335 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 261 76 112 33 90 154 282), lower := (rows 35 134 261 76 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 14 4 14 49 32 69 133 261), good := (rows 506 462 478 462 112 496 64 128 256) }] }

theorem u23335 : Upper (D 6) (R 6) [34,132,257,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23336 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 76 112 34 89 153 281), lower := (rows 35 134 261 76 112 34 64 128 256), losses := [] }

theorem u23336 : Upper (D 6) (R 6) [34,132,257,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23337 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 134 261 76 112 40 83 147 275), lower := (rows 35 134 261 76 112 40 64 128 256), losses := [] }

theorem u23337 : Upper (D 6) (R 6) [34,132,257,68,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23337 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23338 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 76 112 48 75 139 267), lower := (rows 35 134 261 76 112 48 64 128 256), losses := [] }

theorem u23338 : Upper (D 6) (R 6) [34,132,257,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23338 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23339 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 262 13 56 33 80 208 336), lower := (rows 35 134 262 13 56 33 64 128 256), losses := [] }

theorem u23339 : Upper (D 6) (R 6) [34,132,258,5,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23339
end Delivery.IrregularNine14.P06
