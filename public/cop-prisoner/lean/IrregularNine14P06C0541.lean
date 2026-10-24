import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0249
import IrregularNine14P06C0250
import IrregularNine14P06C0251

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32460 : Route 9 := (fun mask => (mask,id))

def c32460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32460 : Upper (D 6) (R 6) [10,96,130,257,36] 13 := by
  apply FastRouting.sound _ _ [10,96,130,257,36] 13 (by decide) (choices 1) [1,4,16,64] r32460 c32460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14955
  · exact u14956
  · exact u14957
  · exact u14958

def b32461 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 134 265 112 53 85 149 277), lower := (rows 11 98 134 265 112 32 64 128 256), losses := [] }

theorem u32461 : Upper (D 6) (R 6) [10,96,130,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32462 : Route 9 := (fun mask => (mask,id))

def c32462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32462 : Upper (D 6) (R 6) [10,96,130,260,5] 13 := by
  apply FastRouting.sound _ _ [10,96,130,260,5] 13 (by decide) (choices 1) [1,16,64] r32462 c32462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14959
  · exact u14960
  · exact u14961

def r32463 : Route 9 := (fun mask => (mask,id))

def c32463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32463 : Upper (D 6) (R 6) [10,96,130,260,33] 13 := by
  apply FastRouting.sound _ _ [10,96,130,260,33] 13 (by decide) (choices 1) [1,4,16,64] r32463 c32463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14962
  · exact u14963
  · exact u14964
  · exact u14965

def r32464 : Route 9 := (fun mask => (mask,id))

def c32464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32464 : Upper (D 6) (R 6) [10,96,130,260,36] 13 := by
  apply FastRouting.sound _ _ [10,96,130,260,36] 13 (by decide) (choices 1) [1,16,64] r32464 c32464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14966
  · exact u14967
  · exact u14968

def b32465 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 134 268 112 53 85 149 277), lower := (rows 11 98 134 268 112 32 64 128 256), losses := [] }

theorem u32465 : Upper (D 6) (R 6) [10,96,130,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32466 : Route 9 := (fun mask => (mask,id))

def c32466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32466 : Upper (D 6) (R 6) [10,96,130,272,5] 13 := by
  apply FastRouting.sound _ _ [10,96,130,272,5] 13 (by decide) (choices 1) [1,4,64] r32466 c32466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14969
  · exact u14970
  · exact u14971

def r32467 : Route 9 := (fun mask => (mask,id))

def c32467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32467 : Upper (D 6) (R 6) [10,96,130,272,33] 13 := by
  apply FastRouting.sound _ _ [10,96,130,272,33] 13 (by decide) (choices 1) [1,4,64] r32467 c32467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14972
  · exact u14973
  · exact u14974

def r32468 : Route 9 := (fun mask => (mask,id))

def c32468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32468 : Upper (D 6) (R 6) [10,96,130,272,36] 13 := by
  apply FastRouting.sound _ _ [10,96,130,272,36] 13 (by decide) (choices 1) [1,4,64] r32468 c32468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14975
  · exact u14976
  · exact u14977

def b32469 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 134 280 112 37 69 133 261), lower := (rows 11 98 134 280 112 32 64 128 256), losses := [] }

theorem u32469 : Upper (D 6) (R 6) [10,96,130,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32470 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 134 296 21 117 85 213 341), lower := (rows 11 98 134 296 21 32 64 128 256), losses := [] }

theorem u32470 : Upper (D 6) (R 6) [10,96,130,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32471 : Route 9 := (fun mask => (mask,id))

def c32471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32471 : Upper (D 6) (R 6) [10,96,130,288,65] 13 := by
  apply FastRouting.sound _ _ [10,96,130,288,65] 13 (by decide) (choices 1) [1,4,16] r32471 c32471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14978
  · exact u14979
  · exact u14980

def r32472 : Route 9 := (fun mask => (mask,id))

def c32472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32472 : Upper (D 6) (R 6) [10,96,130,288,68] 13 := by
  apply FastRouting.sound _ _ [10,96,130,288,68] 13 (by decide) (choices 1) [1,4,16] r32472 c32472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14981
  · exact u14982
  · exact u14983

def b32473 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 148 13 19 356 356 484 356), lower := (rows 11 98 148 13 19 32 64 128 256), losses := [] }

theorem u32473 : Upper (D 6) (R 6) [10,96,144,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32474 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 148 13 21 354 354 482 354), lower := (rows 11 98 148 13 21 32 64 128 256), losses := [] }

theorem u32474 : Upper (D 6) (R 6) [10,96,144,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32475 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 148 13 22 353 353 481 353), lower := (rows 11 98 148 13 22 32 64 128 256), losses := [] }

theorem u32475 : Upper (D 6) (R 6) [10,96,144,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32476 : Route 9 := (fun mask => (mask,id))

def c32476 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32476 : Upper (D 6) (R 6) [10,96,144,5,33] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,33] 13 (by decide) (choices 1) [2,4,64,256] r32476 c32476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14984
  · exact u14985
  · exact u14986
  · exact u14987

def b32477 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 98 148 13 50 357 325 453 325), lower := (rows 11 98 148 13 50 32 64 128 256), losses := [] }

theorem u32477 : Upper (D 6) (R 6) [10,96,144,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32478 : Route 9 := (fun mask => (mask,id))

def c32478 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32478 : Upper (D 6) (R 6) [10,96,144,5,36] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,36] 13 (by decide) (choices 1) [1,2,64,256] r32478 c32478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14988
  · exact u14989
  · exact u14990
  · exact u14991

def b32479 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 148 13 112 295 327 391 263), lower := (rows 11 98 148 13 112 32 64 128 256), losses := [] }

theorem u32479 : Upper (D 6) (R 6) [10,96,144,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32480 : Route 9 := (fun mask => (mask,id))

def c32480 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32480 : Upper (D 6) (R 6) [10,96,144,5,257] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,257] 13 (by decide) (choices 1) [2,4,64] r32480 c32480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14992
  · exact u14993
  · exact u14994

def r32481 : Route 9 := (fun mask => (mask,id))

def c32481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32481 : Upper (D 6) (R 6) [10,96,144,5,258] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,258] 13 (by decide) (choices 1) [1,4,64] r32481 c32481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14995
  · exact u14996
  · exact u14997

def r32482 : Route 9 := (fun mask => (mask,id))

def c32482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32482 : Upper (D 6) (R 6) [10,96,144,5,260] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,260] 13 (by decide) (choices 1) [1,2,64] r32482 c32482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14998
  · exact u14999
  · exact u15000

def r32483 : Route 9 := (fun mask => (mask,id))

def c32483 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32483 : Upper (D 6) (R 6) [10,96,144,5,288] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,288] 13 (by decide) (choices 1) [1,2,4,64] r32483 c32483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15001
  · exact u15002
  · exact u15003
  · exact u15004

def b32484 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 98 148 44 19 357 325 453 325), lower := (rows 11 98 148 44 19 32 64 128 256), losses := [] }

theorem u32484 : Upper (D 6) (R 6) [10,96,144,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32485 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 323, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 98 148 44 21 355 323 451 323), lower := (rows 11 98 148 44 21 32 64 128 256), losses := [] }

theorem u32485 : Upper (D 6) (R 6) [10,96,144,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32486 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 323, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 98 148 44 22 353 321 449 321), lower := (rows 11 98 148 44 22 32 64 128 256), losses := [] }

theorem u32486 : Upper (D 6) (R 6) [10,96,144,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32487 : Route 9 := (fun mask => (mask,id))

def c32487 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32487 : Upper (D 6) (R 6) [10,96,144,36,65] 13 := by
  apply FastRouting.sound _ _ [10,96,144,36,65] 13 (by decide) (choices 1) [1,2,4,256] r32487 c32487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15005
  · exact u15006
  · exact u15007
  · exact u15008

def b32488 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 148 44 82 293 325 389 261), lower := (rows 11 98 148 44 82 32 64 128 256), losses := [] }

theorem u32488 : Upper (D 6) (R 6) [10,96,144,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32489 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 323, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 98 148 44 84 291 323 387 259), lower := (rows 11 98 148 44 84 32 64 128 256), losses := [] }

theorem u32489 : Upper (D 6) (R 6) [10,96,144,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32490 : Route 9 := (fun mask => (mask,id))

def c32490 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32490 : Upper (D 6) (R 6) [10,96,144,36,257] 13 := by
  apply FastRouting.sound _ _ [10,96,144,36,257] 13 (by decide) (choices 1) [1,2,4,64] r32490 c32490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15009
  · exact u15010
  · exact u15011
  · exact u15012

def r32491 : Route 9 := (fun mask => (mask,id))

def c32491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32491 : Upper (D 6) (R 6) [10,96,144,36,258] 13 := by
  apply FastRouting.sound _ _ [10,96,144,36,258] 13 (by decide) (choices 1) [1,4,64] r32491 c32491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15013
  · exact u15014
  · exact u15015

def b32492 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 98 148 44 276 99 67 195 323), lower := (rows 11 98 148 44 276 32 64 128 256), losses := [] }

theorem u32492 : Upper (D 6) (R 6) [10,96,144,36,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32493 : Route 9 := (fun mask => (mask,id))

def c32493 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32493 : Upper (D 6) (R 6) [10,96,144,36,320] 13 := by
  apply FastRouting.sound _ _ [10,96,144,36,320] 13 (by decide) (choices 1) [1,2,4] r32493 c32493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15016
  · exact u15017
  · exact u15018

def b32494 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 148 265 19 100 100 228 356), lower := (rows 11 98 148 265 19 32 64 128 256), losses := [] }

theorem u32494 : Upper (D 6) (R 6) [10,96,144,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32495 : Route 9 := (fun mask => (mask,id))

def c32495 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32495 : Upper (D 6) (R 6) [10,96,144,257,5] 13 := by
  apply FastRouting.sound _ _ [10,96,144,257,5] 13 (by decide) (choices 1) [2,4,64] r32495 c32495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15019
  · exact u15020
  · exact u15021

def r32496 : Route 9 := (fun mask => (mask,id))

def c32496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32496 : Upper (D 6) (R 6) [10,96,144,257,6] 13 := by
  apply FastRouting.sound _ _ [10,96,144,257,6] 13 (by decide) (choices 1) [1,4,64] r32496 c32496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15022
  · exact u15023
  · exact u15024

def r32497 : Route 9 := (fun mask => (mask,id))

def c32497 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32497 : Upper (D 6) (R 6) [10,96,144,257,33] 13 := by
  apply FastRouting.sound _ _ [10,96,144,257,33] 13 (by decide) (choices 1) [2,4,64] r32497 c32497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15025
  · exact u15026
  · exact u15027

def b32498 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 98 148 265 50 101 69 197 325), lower := (rows 11 98 148 265 50 32 64 128 256), losses := [] }

theorem u32498 : Upper (D 6) (R 6) [10,96,144,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32499 : Route 9 := (fun mask => (mask,id))

def c32499 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32499 : Upper (D 6) (R 6) [10,96,144,257,36] 13 := by
  apply FastRouting.sound _ _ [10,96,144,257,36] 13 (by decide) (choices 1) [1,2,4,64] r32499 c32499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15028
  · exact u15029
  · exact u15030
  · exact u15031

def b32500 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 148 265 112 39 71 135 263), lower := (rows 11 98 148 265 112 32 64 128 256), losses := [] }

theorem u32500 : Upper (D 6) (R 6) [10,96,144,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32501 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 148 268 19 101 101 229 357), lower := (rows 11 98 148 268 19 32 64 128 256), losses := [] }

theorem u32501 : Upper (D 6) (R 6) [10,96,144,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32502 : Route 9 := (fun mask => (mask,id))

def c32502 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32502 : Upper (D 6) (R 6) [10,96,144,260,5] 13 := by
  apply FastRouting.sound _ _ [10,96,144,260,5] 13 (by decide) (choices 1) [1,2,64] r32502 c32502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15032
  · exact u15033
  · exact u15034

def r32503 : Route 9 := (fun mask => (mask,id))

def c32503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32503 : Upper (D 6) (R 6) [10,96,144,260,6] 13 := by
  apply FastRouting.sound _ _ [10,96,144,260,6] 13 (by decide) (choices 1) [1,64] r32503 c32503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15035
  · exact u15036

def r32504 : Route 9 := (fun mask => (mask,id))

def c32504 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32504 : Upper (D 6) (R 6) [10,96,144,260,33] 13 := by
  apply FastRouting.sound _ _ [10,96,144,260,33] 13 (by decide) (choices 1) [1,2,4,64] r32504 c32504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15037
  · exact u15038
  · exact u15039
  · exact u15040

def b32505 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 98 148 268 50 101 69 197 325), lower := (rows 11 98 148 268 50 32 64 128 256), losses := [] }

theorem u32505 : Upper (D 6) (R 6) [10,96,144,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32506 : Route 9 := (fun mask => (mask,id))

def c32506 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32506 : Upper (D 6) (R 6) [10,96,144,260,36] 13 := by
  apply FastRouting.sound _ _ [10,96,144,260,36] 13 (by decide) (choices 1) [1,2,64] r32506 c32506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15041
  · exact u15042
  · exact u15043

def b32507 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 148 268 112 39 71 135 263), lower := (rows 11 98 148 268 112 32 64 128 256), losses := [] }

theorem u32507 : Upper (D 6) (R 6) [10,96,144,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32508 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 98 148 296 19 101 69 197 325), lower := (rows 11 98 148 296 19 32 64 128 256), losses := [] }

theorem u32508 : Upper (D 6) (R 6) [10,96,144,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32509 : Route 9 := (fun mask => (mask,id))

def c32509 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32509 : Upper (D 6) (R 6) [10,96,144,288,5] 13 := by
  apply FastRouting.sound _ _ [10,96,144,288,5] 13 (by decide) (choices 1) [1,2,4,64] r32509 c32509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15044
  · exact u15045
  · exact u15046
  · exact u15047

def r32510 : Route 9 := (fun mask => (mask,id))

def c32510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32510 : Upper (D 6) (R 6) [10,96,144,288,6] 13 := by
  apply FastRouting.sound _ _ [10,96,144,288,6] 13 (by decide) (choices 1) [1,4,64] r32510 c32510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15048
  · exact u15049
  · exact u15050

def r32511 : Route 9 := (fun mask => (mask,id))

def c32511 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32511 : Upper (D 6) (R 6) [10,96,144,288,65] 13 := by
  apply FastRouting.sound _ _ [10,96,144,288,65] 13 (by decide) (choices 1) [1,2,4] r32511 c32511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15051
  · exact u15052
  · exact u15053

def b32512 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 148 296 82 37 69 133 261), lower := (rows 11 98 148 296 82 32 64 128 256), losses := [] }

theorem u32512 : Upper (D 6) (R 6) [10,96,144,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32513 : Route 9 := (fun mask => (mask,id))

def c32513 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32513 : Upper (D 6) (R 6) [10,96,144,288,68] 13 := by
  apply FastRouting.sound _ _ [10,96,144,288,68] 13 (by decide) (choices 1) [1,2,4] r32513 c32513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15054
  · exact u15055
  · exact u15056

def b32514 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 164 13 19 372 340 468 340), lower := (rows 11 98 164 13 19 32 64 128 256), losses := [] }

theorem u32514 : Upper (D 6) (R 6) [10,96,160,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32515 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 164 13 21 370 338 466 338), lower := (rows 11 98 164 13 21 32 64 128 256), losses := [] }

theorem u32515 : Upper (D 6) (R 6) [10,96,160,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32516 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 9, targets := 32 },{ cop := 4, region := 9, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 164 13 22 369 337 465 337), lower := (rows 11 98 164 13 22 32 64 128 256), losses := [] }

theorem u32516 : Upper (D 6) (R 6) [10,96,160,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32517 : Route 9 := (fun mask => (mask,id))

def c32517 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32517 : Upper (D 6) (R 6) [10,96,160,5,65] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5,65] 13 (by decide) (choices 1) [2,4,16,256] r32517 c32517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15057
  · exact u15058
  · exact u15059
  · exact u15060

def b32518 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 164 13 82 309 341 405 277), lower := (rows 11 98 164 13 82 32 64 128 256), losses := [] }

theorem u32518 : Upper (D 6) (R 6) [10,96,160,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32519 : Route 9 := (fun mask => (mask,id))

def c32519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32519 : Upper (D 6) (R 6) [10,96,160,5,68] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5,68] 13 (by decide) (choices 1) [1,2,16,256] r32519 c32519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15061
  · exact u15062
  · exact u15063
  · exact u15064

#print axioms u32519
end Delivery.IrregularNine14.P06
