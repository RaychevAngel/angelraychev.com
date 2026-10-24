import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0316
import IrregularNine14P07C0317
import IrregularNine14P07C0318

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34380 : Route 9 := (fun mask => (mask,id))

def c34380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34380 : Upper (D 7) (R 7) [34,68,24,160,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160,384] 13 (by decide) (choices 1) [1,2,64] r34380 c34380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19013
  · exact u19014
  · exact u19015

def r34381 : Route 9 := (fun mask => (mask,id))

def c34381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34381 : Upper (D 7) (R 7) [34,68,24,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,192,257] 13 (by decide) (choices 1) [1,2,128] r34381 c34381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19016
  · exact u19017
  · exact u19018

def r34382 : Route 9 := (fun mask => (mask,id))

def c34382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34382 : Upper (D 7) (R 7) [34,68,24,192,258] 13 := by
  apply FastRouting.sound _ _ [34,68,24,192,258] 13 (by decide) (choices 1) [1,128] r34382 c34382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19019
  · exact u19020

def r34383 : Route 9 := (fun mask => (mask,id))

def c34383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34383 : Upper (D 7) (R 7) [34,68,24,192,288] 13 := by
  apply FastRouting.sound _ _ [34,68,24,192,288] 13 (by decide) (choices 1) [1,2,128] r34383 c34383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19021
  · exact u19022
  · exact u19023

def b34384 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 70 28 200 400 35 99 163 291), lower := (rows 35 70 28 200 400 32 64 128 256), losses := [] }

theorem u34384 : Upper (D 7) (R 7) [34,68,24,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34385 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 70 44 25 19 480 448 448 448), lower := (rows 35 70 44 25 19 32 64 128 256), losses := [] }

theorem u34385 : Upper (D 7) (R 7) [34,68,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34386 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 44 25 81 418 450 386 386), lower := (rows 35 70 44 25 81 32 64 128 256), losses := [] }

theorem u34386 : Upper (D 7) (R 7) [34,68,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34387 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 44 25 82 417 449 385 385), lower := (rows 35 70 44 25 82 32 64 128 256), losses := [] }

theorem u34387 : Upper (D 7) (R 7) [34,68,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34388 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 44 25 145 482 450 450 450), lower := (rows 35 70 44 25 145 32 64 128 256), losses := [] }

theorem u34388 : Upper (D 7) (R 7) [34,68,40,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34389 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 484, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 70 44 25 146 481 449 449 449), lower := (rows 35 70 44 25 146 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 21 0 73 137 265), good := (rows 475 86 478 473 146 0 64 128 256) }] }

theorem u34389 : Upper (D 7) (R 7) [34,68,40,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34390 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 44 25 208 419 451 387 387), lower := (rows 35 70 44 25 208 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 35 0 131 259), good := (rows 419 423 44 445 144 32 0 128 256) }] }

theorem u34390 : Upper (D 7) (R 7) [34,68,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34391 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 44 25 273 226 194 194 450), lower := (rows 35 70 44 25 273 32 64 128 256), losses := [] }

theorem u34391 : Upper (D 7) (R 7) [34,68,40,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34392 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 228, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 70 44 25 274 225 193 193 449), lower := (rows 35 70 44 25 274 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 21 0 73 137 265), good := (rows 475 86 478 473 274 0 64 128 256) }] }

theorem u34392 : Upper (D 7) (R 7) [34,68,40,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34393 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 44 25 336 163 195 131 387), lower := (rows 35 70 44 25 336 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 35 0 131 259), good := (rows 419 423 44 445 272 32 0 128 256) }] }

theorem u34393 : Upper (D 7) (R 7) [34,68,40,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34394 : Route 9 := (fun mask => (mask,id))

def c34394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34394 : Upper (D 7) (R 7) [34,68,40,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17,384] 13 (by decide) (choices 1) [1,2,64,128] r34394 c34394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19024
  · exact u19025
  · exact u19026
  · exact u19027

def b34395 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 44 26 81 417 449 385 385), lower := (rows 35 70 44 26 81 32 64 128 256), losses := [] }

theorem u34395 : Upper (D 7) (R 7) [34,68,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34396 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 2 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 35 70 44 26 145 481 449 449 449), lower := (rows 35 70 44 26 145 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 497 68 44 508 497 32 64 128 256) }] }

theorem u34396 : Upper (D 7) (R 7) [34,68,40,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34397 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 44 26 208 417 449 385 385), lower := (rows 35 70 44 26 208 32 64 128 256), losses := [] }

theorem u34397 : Upper (D 7) (R 7) [34,68,40,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34398 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 2 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 35 70 44 26 273 225 193 193 449), lower := (rows 35 70 44 26 273 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 497 68 44 508 497 32 64 128 256) }] }

theorem u34398 : Upper (D 7) (R 7) [34,68,40,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34399 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 44 26 336 161 193 129 385), lower := (rows 35 70 44 26 336 32 64 128 256), losses := [] }

theorem u34399 : Upper (D 7) (R 7) [34,68,40,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34400 : Route 9 := (fun mask => (mask,id))

def c34400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34400 : Upper (D 7) (R 7) [34,68,40,18,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18,384] 13 (by decide) (choices 1) [1,64,128] r34400 c34400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19028
  · exact u19029
  · exact u19030

def b34401 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 35 70 44 137 19 496 464 464 464), lower := (rows 35 70 44 137 19 32 64 128 256), losses := [] }

theorem u34401 : Upper (D 7) (R 7) [34,68,40,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34402 : Route 9 := (fun mask => (mask,id))

def c34402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u34402 : Upper (D 7) (R 7) [34,68,40,129,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,65] 13 (by decide) (choices 1) [2,16,128,256] r34402 c34402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19031
  · exact u19032
  · exact u19033
  · exact u19034

def b34403 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 44 137 82 433 465 401 401), lower := (rows 35 70 44 137 82 32 64 128 256), losses := [] }

theorem u34403 : Upper (D 7) (R 7) [34,68,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34404 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 70 44 137 145 370 338 466 338), lower := (rows 35 70 44 137 145 32 64 128 256), losses := [] }

theorem u34404 : Upper (D 7) (R 7) [34,68,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34405 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,5),(3,5),(4,5)], upper := (rows 35 70 44 137 146 369 337 465 337), lower := (rows 35 70 44 137 146 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 21 0 73 137 265), good := (rows 475 86 478 473 146 0 64 128 256) }] }

theorem u34405 : Upper (D 7) (R 7) [34,68,40,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34406 : Route 9 := (fun mask => (mask,id))

def c34406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34406 : Upper (D 7) (R 7) [34,68,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,192] 13 (by decide) (choices 1) [1,2,16,256] r34406 c34406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19035
  · exact u19036
  · exact u19037
  · exact u19038

def r34407 : Route 9 := (fun mask => (mask,id))

def c34407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34407 : Upper (D 7) (R 7) [34,68,40,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,257] 13 (by decide) (choices 1) [2,16,64,128] r34407 c34407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19039
  · exact u19040
  · exact u19041
  · exact u19042

def r34408 : Route 9 := (fun mask => (mask,id))

def c34408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34408 : Upper (D 7) (R 7) [34,68,40,129,258] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,258] 13 (by decide) (choices 1) [1,16,64,128] r34408 c34408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19043
  · exact u19044
  · exact u19045
  · exact u19046

def r34409 : Route 9 := (fun mask => (mask,id))

def c34409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34409 : Upper (D 7) (R 7) [34,68,40,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,320] 13 (by decide) (choices 1) [1,2,16,128] r34409 c34409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19047
  · exact u19048
  · exact u19049
  · exact u19050

def r34410 : Route 9 := (fun mask => (mask,id))

def c34410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34410 : Upper (D 7) (R 7) [34,68,40,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,384] 13 (by decide) (choices 1) [1,2,16,64] r34410 c34410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19051
  · exact u19052
  · exact u19053
  · exact u19054

def r34411 : Route 9 := (fun mask => (mask,id))

def c34411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u34411 : Upper (D 7) (R 7) [34,68,40,130,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,65] 13 (by decide) (choices 1) [1,16,128,256] r34411 c34411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19055
  · exact u19056
  · exact u19057
  · exact u19058

def r34412 : Route 9 := (fun mask => (mask,id))

def c34412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u34412 : Upper (D 7) (R 7) [34,68,40,130,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,129] 13 (by decide) (choices 1) [1,16,64,256] r34412 c34412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19059
  · exact u19060
  · exact u19061
  · exact u19062

def r34413 : Route 9 := (fun mask => (mask,id))

def c34413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34413 : Upper (D 7) (R 7) [34,68,40,130,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,192] 13 (by decide) (choices 1) [1,16,256] r34413 c34413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19063
  · exact u19064
  · exact u19065

def r34414 : Route 9 := (fun mask => (mask,id))

def c34414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34414 : Upper (D 7) (R 7) [34,68,40,130,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,257] 13 (by decide) (choices 1) [1,16,64,128] r34414 c34414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19066
  · exact u19067
  · exact u19068
  · exact u19069

def r34415 : Route 9 := (fun mask => (mask,id))

def c34415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34415 : Upper (D 7) (R 7) [34,68,40,130,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,320] 13 (by decide) (choices 1) [1,16,128] r34415 c34415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19070
  · exact u19071
  · exact u19072

def r34416 : Route 9 := (fun mask => (mask,id))

def c34416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34416 : Upper (D 7) (R 7) [34,68,40,130,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130,384] 13 (by decide) (choices 1) [1,16,64] r34416 c34416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19073
  · exact u19074
  · exact u19075

def b34417 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 35 70 44 152 19 481 449 449 449), lower := (rows 35 70 44 152 19 32 64 128 256), losses := [] }

theorem u34417 : Upper (D 7) (R 7) [34,68,40,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34418 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 44 152 81 419 451 387 387), lower := (rows 35 70 44 152 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 35 0 131 259), good := (rows 419 423 44 156 445 32 0 128 256) }] }

theorem u34418 : Upper (D 7) (R 7) [34,68,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34419 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 44 152 82 417 449 385 385), lower := (rows 35 70 44 152 82 32 64 128 256), losses := [] }

theorem u34419 : Upper (D 7) (R 7) [34,68,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34420 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 44 152 145 355 323 451 323), lower := (rows 35 70 44 152 145 32 64 128 256), losses := [] }

theorem u34420 : Upper (D 7) (R 7) [34,68,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34421 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 44 152 146 353 321 449 321), lower := (rows 35 70 44 152 146 32 64 128 256), losses := [] }

theorem u34421 : Upper (D 7) (R 7) [34,68,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34422 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 44 152 208 291 323 387 259), lower := (rows 35 70 44 152 208 32 64 128 256), losses := [] }

theorem u34422 : Upper (D 7) (R 7) [34,68,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34423 : Route 9 := (fun mask => (mask,id))

def c34423 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34423 : Upper (D 7) (R 7) [34,68,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,257] 13 (by decide) (choices 1) [1,2,64,128] r34423 c34423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19076
  · exact u19077
  · exact u19078
  · exact u19079

def r34424 : Route 9 := (fun mask => (mask,id))

def c34424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34424 : Upper (D 7) (R 7) [34,68,40,144,258] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,258] 13 (by decide) (choices 1) [1,64,128] r34424 c34424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19080
  · exact u19081
  · exact u19082

def r34425 : Route 9 := (fun mask => (mask,id))

def c34425 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34425 : Upper (D 7) (R 7) [34,68,40,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,320] 13 (by decide) (choices 1) [1,2,128] r34425 c34425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19083
  · exact u19084
  · exact u19085

def b34426 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 70 44 152 400 99 67 195 323), lower := (rows 35 70 44 152 400 32 64 128 256), losses := [] }

theorem u34426 : Upper (D 7) (R 7) [34,68,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34427 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 35 70 44 265 19 240 208 208 464), lower := (rows 35 70 44 265 19 32 64 128 256), losses := [] }

theorem u34427 : Upper (D 7) (R 7) [34,68,40,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34428 : Route 9 := (fun mask => (mask,id))

def c34428 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34428 : Upper (D 7) (R 7) [34,68,40,257,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,65] 13 (by decide) (choices 1) [2,16,128] r34428 c34428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19086
  · exact u19087
  · exact u19088

def b34429 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 44 265 82 177 209 145 401), lower := (rows 35 70 44 265 82 32 64 128 256), losses := [] }

theorem u34429 : Upper (D 7) (R 7) [34,68,40,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34430 : Route 9 := (fun mask => (mask,id))

def c34430 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34430 : Upper (D 7) (R 7) [34,68,40,257,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,129] 13 (by decide) (choices 1) [2,16,64,128] r34430 c34430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19089
  · exact u19090
  · exact u19091
  · exact u19092

def r34431 : Route 9 := (fun mask => (mask,id))

def c34431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34431 : Upper (D 7) (R 7) [34,68,40,257,130] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,130] 13 (by decide) (choices 1) [1,16,64,128] r34431 c34431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19093
  · exact u19094
  · exact u19095
  · exact u19096

def r34432 : Route 9 := (fun mask => (mask,id))

def c34432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34432 : Upper (D 7) (R 7) [34,68,40,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,192] 13 (by decide) (choices 1) [1,2,16,128] r34432 c34432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19097
  · exact u19098
  · exact u19099
  · exact u19100

def r34433 : Route 9 := (fun mask => (mask,id))

def c34433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34433 : Upper (D 7) (R 7) [34,68,40,258,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,258,65] 13 (by decide) (choices 1) [1,16,128] r34433 c34433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19101
  · exact u19102
  · exact u19103

def r34434 : Route 9 := (fun mask => (mask,id))

def c34434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u34434 : Upper (D 7) (R 7) [34,68,40,258,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,258,129] 13 (by decide) (choices 1) [1,16,64,128] r34434 c34434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19104
  · exact u19105
  · exact u19106
  · exact u19107

def r34435 : Route 9 := (fun mask => (mask,id))

def c34435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34435 : Upper (D 7) (R 7) [34,68,40,258,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,258,192] 13 (by decide) (choices 1) [1,16,128] r34435 c34435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19108
  · exact u19109
  · exact u19110

def b34436 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 35 70 44 280 19 225 193 193 449), lower := (rows 35 70 44 280 19 32 64 128 256), losses := [] }

theorem u34436 : Upper (D 7) (R 7) [34,68,40,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34437 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 44 280 81 163 195 131 387), lower := (rows 35 70 44 280 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 35 0 131 259), good := (rows 419 423 44 284 445 32 0 128 256) }] }

theorem u34437 : Upper (D 7) (R 7) [34,68,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34438 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 44 280 82 161 193 129 385), lower := (rows 35 70 44 280 82 32 64 128 256), losses := [] }

theorem u34438 : Upper (D 7) (R 7) [34,68,40,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34439 : Route 9 := (fun mask => (mask,id))

def c34439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34439 : Upper (D 7) (R 7) [34,68,40,272,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,272,129] 13 (by decide) (choices 1) [1,2,64,128] r34439 c34439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19111
  · exact u19112
  · exact u19113
  · exact u19114

#print axioms u34439
end Delivery.IrregularNine14.P07
