import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0110
import IrregularNine14P06C0111

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22260 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 25 276 96 78 142 270), lower := (rows 35 131 100 25 276 96 64 128 256), losses := [] }

theorem u22260 : Upper (D 6) (R 6) [34,129,96,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22261 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 25 280 34 68 196 324), lower := (rows 35 131 100 25 280 34 64 128 256), losses := [] }

theorem u22261 : Upper (D 6) (R 6) [34,129,96,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22262 : PairBound 9 := { available := 70, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 25 280 36 70 198 326), lower := (rows 35 131 100 25 280 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 79 8 24 127 67 131 259), good := (rows 486 486 100 508 316 36 100 128 256) }] }

theorem u22262 : Upper (D 6) (R 6) [34,129,96,17,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22263 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 25 280 96 70 134 262), lower := (rows 35 131 100 25 280 96 64 128 256), losses := [] }

theorem u22263 : Upper (D 6) (R 6) [34,129,96,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22264 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 25 336 34 76 140 268), lower := (rows 35 131 100 25 336 34 64 128 256), losses := [] }

theorem u22264 : Upper (D 6) (R 6) [34,129,96,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22265 : Route 9 := (fun mask => (mask,id))

def c22265 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22265 : Upper (D 6) (R 6) [34,129,96,17,320,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,17,320,4] 13 (by decide) (choices 1) [2,4,8] r22265 c22265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6653
  · exact u6654
  · exact u6655

def b22266 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 100 25 336 40 70 134 262), lower := (rows 35 131 100 25 336 40 64 128 256), losses := [] }

theorem u22266 : Upper (D 6) (R 6) [34,129,96,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22266 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22267 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 26 28 33 324 452 324), lower := (rows 35 131 100 26 28 33 64 128 256), losses := [] }

theorem u22267 : Upper (D 6) (R 6) [34,129,96,18,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22268 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 450, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 131 100 26 28 36 321 449 321), lower := (rows 35 131 100 26 28 36 64 128 256), losses := [] }

theorem u22268 : Upper (D 6) (R 6) [34,129,96,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22269 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 26 28 96 325 389 261), lower := (rows 35 131 100 26 28 96 64 128 256), losses := [] }

theorem u22269 : Upper (D 6) (R 6) [34,129,96,18,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22270 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 26 28 288 69 197 325), lower := (rows 35 131 100 26 28 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 299 67 131 259), good := (rows 485 485 100 508 60 288 64 128 288) }] }

theorem u22270 : Upper (D 6) (R 6) [34,129,96,18,12,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22270 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22271 : Route 9 := (fun mask => (mask,id))

def c22271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u22271 : Upper (D 6) (R 6) [34,129,96,18,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18,65,4] 13 (by decide) (choices 1) [4,8,256] r22271 c22271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6656
  · exact u6657
  · exact u6658

def b22272 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 26 81 40 324 388 260), lower := (rows 35 131 100 26 81 40 64 128 256), losses := [] }

theorem u22272 : Upper (D 6) (R 6) [34,129,96,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22272 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22273 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 26 81 288 76 140 268), lower := (rows 35 131 100 26 81 288 64 128 256), losses := [] }

theorem u22273 : Upper (D 6) (R 6) [34,129,96,18,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22273 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22274 : Route 9 := (fun mask => (mask,id))

def c22274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22274 : Upper (D 6) (R 6) [34,129,96,18,257,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18,257,4] 13 (by decide) (choices 1) [4,8] r22274 c22274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6659
  · exact u6660

def b22275 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 26 273 40 68 196 324), lower := (rows 35 131 100 26 273 40 64 128 256), losses := [] }

theorem u22275 : Upper (D 6) (R 6) [34,129,96,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22275 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22276 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 26 273 96 76 140 268), lower := (rows 35 131 100 26 273 96 64 128 256), losses := [] }

theorem u22276 : Upper (D 6) (R 6) [34,129,96,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22277 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 26 276 33 76 204 332), lower := (rows 35 131 100 26 276 33 64 128 256), losses := [] }

theorem u22277 : Upper (D 6) (R 6) [34,129,96,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22278 : PairBound 9 := { available := 73, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 100 26 276 36 73 201 329), lower := (rows 35 131 100 26 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 35 131 36 59 308 36 0 128 256) }] }

theorem u22278 : Upper (D 6) (R 6) [34,129,96,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22279 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 26 276 40 69 197 325), lower := (rows 35 131 100 26 276 40 64 128 256), losses := [] }

theorem u22279 : Upper (D 6) (R 6) [34,129,96,18,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22279 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22280 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 26 276 96 77 141 269), lower := (rows 35 131 100 26 276 96 64 128 256), losses := [] }

theorem u22280 : Upper (D 6) (R 6) [34,129,96,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22281 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 26 280 33 68 196 324), lower := (rows 35 131 100 26 280 33 64 128 256), losses := [] }

theorem u22281 : Upper (D 6) (R 6) [34,129,96,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22282 : PairBound 9 := { available := 69, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 131 100 26 280 36 69 197 325), lower := (rows 35 131 100 26 280 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 79 8 24 127 67 131 259), good := (rows 485 485 100 508 316 36 100 128 256) }] }

theorem u22282 : Upper (D 6) (R 6) [34,129,96,18,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22283 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 26 280 96 69 133 261), lower := (rows 35 131 100 26 280 96 64 128 256), losses := [] }

theorem u22283 : Upper (D 6) (R 6) [34,129,96,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22284 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 26 336 33 76 140 268), lower := (rows 35 131 100 26 336 33 64 128 256), losses := [] }

theorem u22284 : Upper (D 6) (R 6) [34,129,96,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22285 : Route 9 := (fun mask => (mask,id))

def c22285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22285 : Upper (D 6) (R 6) [34,129,96,18,320,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18,320,4] 13 (by decide) (choices 1) [1,4,8] r22285 c22285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6661
  · exact u6662
  · exact u6663

def b22286 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 26 336 40 69 133 261), lower := (rows 35 131 100 26 336 40 64 128 256), losses := [] }

theorem u22286 : Upper (D 6) (R 6) [34,129,96,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22286 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22287 : PairBound 9 := { available := 268, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 28 81 34 332 396 268), lower := (rows 35 131 100 28 81 34 64 128 256), losses := [] }

theorem u22287 : Upper (D 6) (R 6) [34,129,96,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22288 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 100 28 81 36 330 394 266), lower := (rows 35 131 100 28 81 36 64 128 256), losses := [] }

theorem u22288 : Upper (D 6) (R 6) [34,129,96,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22289 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 28 81 40 326 390 262), lower := (rows 35 131 100 28 81 40 64 128 256), losses := [] }

theorem u22289 : Upper (D 6) (R 6) [34,129,96,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22289 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22290 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 28 81 288 78 142 270), lower := (rows 35 131 100 28 81 288 64 128 256), losses := [] }

theorem u22290 : Upper (D 6) (R 6) [34,129,96,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22290 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22291 : PairBound 9 := { available := 268, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 28 82 33 332 396 268), lower := (rows 35 131 100 28 82 33 64 128 256), losses := [] }

theorem u22291 : Upper (D 6) (R 6) [34,129,96,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22292 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 100 28 82 36 329 393 265), lower := (rows 35 131 100 28 82 36 64 128 256), losses := [] }

theorem u22292 : Upper (D 6) (R 6) [34,129,96,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22293 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 28 82 40 325 389 261), lower := (rows 35 131 100 28 82 40 64 128 256), losses := [] }

theorem u22293 : Upper (D 6) (R 6) [34,129,96,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22293 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22294 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 28 82 288 77 141 269), lower := (rows 35 131 100 28 82 288 64 128 256), losses := [] }

theorem u22294 : Upper (D 6) (R 6) [34,129,96,20,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22294 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22295 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 28 273 34 76 204 332), lower := (rows 35 131 100 28 273 34 64 128 256), losses := [] }

theorem u22295 : Upper (D 6) (R 6) [34,129,96,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22296 : Route 9 := (fun mask => (mask,id))

def c22296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22296 : Upper (D 6) (R 6) [34,129,96,20,257,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,20,257,4] 13 (by decide) (choices 1) [2,8] r22296 c22296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6664
  · exact u6665

def b22297 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 100 28 273 40 70 198 326), lower := (rows 35 131 100 28 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 21 24 16 56 67 131 259), good := (rows 486 454 100 60 508 40 64 128 256) }] }

theorem u22297 : Upper (D 6) (R 6) [34,129,96,20,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22297 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22298 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 28 273 96 78 142 270), lower := (rows 35 131 100 28 273 96 64 128 256), losses := [] }

theorem u22298 : Upper (D 6) (R 6) [34,129,96,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22299 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 28 274 33 76 204 332), lower := (rows 35 131 100 28 274 33 64 128 256), losses := [] }

theorem u22299 : Upper (D 6) (R 6) [34,129,96,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22300 : Route 9 := (fun mask => (mask,id))

def c22300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22300 : Upper (D 6) (R 6) [34,129,96,20,258,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,20,258,4] 13 (by decide) (choices 1) [1,8] r22300 c22300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6666
  · exact u6667

def b22301 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 100 28 274 40 69 197 325), lower := (rows 35 131 100 28 274 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 21 24 16 56 67 131 259), good := (rows 485 453 100 60 508 40 64 128 256) }] }

theorem u22301 : Upper (D 6) (R 6) [34,129,96,20,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22301 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22302 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 28 274 96 77 141 269), lower := (rows 35 131 100 28 274 96 64 128 256), losses := [] }

theorem u22302 : Upper (D 6) (R 6) [34,129,96,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22303 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 28 280 33 70 198 326), lower := (rows 35 131 100 28 280 33 64 128 256), losses := [] }

theorem u22303 : Upper (D 6) (R 6) [34,129,96,20,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22304 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 28 280 34 69 197 325), lower := (rows 35 131 100 28 280 34 64 128 256), losses := [] }

theorem u22304 : Upper (D 6) (R 6) [34,129,96,20,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22305 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 131 100 28 280 36 67 195 323), lower := (rows 35 131 100 28 280 36 64 128 256), losses := [] }

theorem u22305 : Upper (D 6) (R 6) [34,129,96,20,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22306 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 28 280 96 71 135 263), lower := (rows 35 131 100 28 280 96 64 128 256), losses := [] }

theorem u22306 : Upper (D 6) (R 6) [34,129,96,20,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22307 : PairBound 9 := { available := 14, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 28 336 33 78 142 270), lower := (rows 35 131 100 28 336 33 64 128 256), losses := [] }

theorem u22307 : Upper (D 6) (R 6) [34,129,96,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22308 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 28 336 34 77 141 269), lower := (rows 35 131 100 28 336 34 64 128 256), losses := [] }

theorem u22308 : Upper (D 6) (R 6) [34,129,96,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22309 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 100 28 336 36 75 139 267), lower := (rows 35 131 100 28 336 36 64 128 256), losses := [] }

theorem u22309 : Upper (D 6) (R 6) [34,129,96,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22310 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 28 336 40 71 135 263), lower := (rows 35 131 100 28 336 40 64 128 256), losses := [] }

theorem u22310 : Upper (D 6) (R 6) [34,129,96,20,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22310 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22311 : Route 9 := (fun mask => (mask,id))

def c22311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22311 : Upper (D 6) (R 6) [34,129,96,65,258,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,65,258,4] 13 (by decide) (choices 1) [4,8,16] r22311 c22311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6668
  · exact u6669
  · exact u6670

def b22312 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 73 274 40 84 148 276), lower := (rows 35 131 100 73 274 40 64 128 256), losses := [] }

theorem u22312 : Upper (D 6) (R 6) [34,129,96,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22312 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22313 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 100 73 274 48 76 140 268), lower := (rows 35 131 100 73 274 48 64 128 256), losses := [] }

theorem u22313 : Upper (D 6) (R 6) [34,129,96,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22313 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22314 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 73 276 34 92 156 284), lower := (rows 35 131 100 73 276 34 64 128 256), losses := [] }

theorem u22314 : Upper (D 6) (R 6) [34,129,96,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22315 : Route 9 := (fun mask => (mask,id))

def c22315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22315 : Upper (D 6) (R 6) [34,129,96,65,260,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,65,260,4] 13 (by decide) (choices 1) [2,8,16] r22315 c22315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6671
  · exact u6672
  · exact u6673

def b22316 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 73 276 40 86 150 278), lower := (rows 35 131 100 73 276 40 64 128 256), losses := [] }

theorem u22316 : Upper (D 6) (R 6) [34,129,96,65,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22316 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22317 : Route 9 := (fun mask => (mask,id))

def c22317 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22317 : Upper (D 6) (R 6) [34,129,96,65,260,16] 13 := by
  apply FastRouting.sound _ _ [34,129,96,65,260,16] 13 (by decide) (choices 1) [2,4,8] r22317 c22317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6674
  · exact u6675
  · exact u6676

def b22318 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 73 280 34 84 148 276), lower := (rows 35 131 100 73 280 34 64 128 256), losses := [] }

theorem u22318 : Upper (D 6) (R 6) [34,129,96,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22319 : Route 9 := (fun mask => (mask,id))

def c22319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22319 : Upper (D 6) (R 6) [34,129,96,65,264,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,65,264,4] 13 (by decide) (choices 1) [2,4,16] r22319 c22319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6677
  · exact u6678
  · exact u6679

#print axioms u22319
end Delivery.IrregularNine14.P06
