import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0001

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b480 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 22 164 392 272 40 67 195 323), lower := (rows 113 22 164 392 272 40 64 128 256), losses := [] }

theorem u480 : Upper (D 2) (R 2) [112,20,160,384,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b480
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b481 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 392 272 96 75 139 267), lower := (rows 113 22 164 392 272 96 64 128 256), losses := [] }

theorem u481 : Upper (D 2) (R 2) [112,20,160,384,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b481
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b482 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 130, targets := 256 }], pairs := [(1,8)], upper := (rows 113 131 140 266 20 288 112 240 368), lower := (rows 113 131 140 266 20 288 64 128 256), losses := [] }

theorem u482 : Upper (D 2) (R 2) [112,129,136,258,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b482
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 131 140 266 48 288 84 212 340), lower := (rows 113 131 140 266 48 288 64 128 256), losses := [] }

theorem u483 : Upper (D 2) (R 2) [112,129,136,258,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b483
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 131 140 266 80 288 116 180 308), lower := (rows 113 131 140 266 80 288 64 128 256), losses := [] }

theorem u484 : Upper (D 2) (R 2) [112,129,136,258,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b484
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b485 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 394, targets := 16 }], pairs := [(1,4)], upper := (rows 113 131 148 266 272 36 104 232 360), lower := (rows 113 131 148 266 272 36 64 128 256), losses := [] }

theorem u485 : Upper (D 2) (R 2) [112,129,144,258,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b485
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b486 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 131 148 266 272 40 100 228 356), lower := (rows 113 131 148 266 272 40 64 128 256), losses := [] }

theorem u486 : Upper (D 2) (R 2) [112,129,144,258,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b486
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b487 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 131 148 266 272 96 108 172 300), lower := (rows 113 131 148 266 272 96 64 128 256), losses := [] }

theorem u487 : Upper (D 2) (R 2) [112,129,144,258,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b487
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r488 : Route 9 := (fun mask => (mask,id))

def c488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u488 : Upper (D 2) (R 2) [112,129,144,260,256,2] 13 := by
  apply FastRouting.sound _ _ [112,129,144,260,256,2] 13 (by decide) (choices 1) [8,32] r488 c488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u75
  · exact u76

def b489 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 130, targets := 256 }], pairs := [(1,8)], upper := (rows 113 131 148 268 272 40 98 226 354), lower := (rows 113 131 148 268 272 40 64 128 256), losses := [] }

theorem u489 : Upper (D 2) (R 2) [112,129,144,260,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b489
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 131 148 268 272 96 106 170 298), lower := (rows 113 131 148 268 272 96 64 128 256), losses := [] }

theorem u490 : Upper (D 2) (R 2) [112,129,144,260,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b490
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 296 272 34 76 204 332), lower := (rows 113 131 148 296 272 34 64 128 256), losses := [] }

theorem u491 : Upper (D 2) (R 2) [112,129,144,288,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b491
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 394, targets := 16 }], pairs := [(1,4)], upper := (rows 113 131 148 296 272 36 74 202 330), lower := (rows 113 131 148 296 272 36 64 128 256), losses := [] }

theorem u492 : Upper (D 2) (R 2) [112,129,144,288,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b492
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 134, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 148 296 272 40 70 198 326), lower := (rows 113 131 148 296 272 40 64 128 256), losses := [] }

theorem u493 : Upper (D 2) (R 2) [112,129,144,288,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b493
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 131 148 296 272 96 78 142 270), lower := (rows 113 131 148 296 272 96 64 128 256), losses := [] }

theorem u494 : Upper (D 2) (R 2) [112,129,144,288,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b494
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 113 131 262 392 20 40 112 240 368), lower := (rows 113 131 262 392 20 40 64 128 256), losses := [] }

theorem u495 : Upper (D 2) (R 2) [112,129,258,384,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b495
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b496 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 394, targets := 16 }], pairs := [(1,4)], upper := (rows 113 131 262 392 20 48 104 232 360), lower := (rows 113 131 262 392 20 48 64 128 256), losses := [] }

theorem u496 : Upper (D 2) (R 2) [112,129,258,384,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b496
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b497 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 262 392 20 96 120 184 312), lower := (rows 113 131 262 392 20 96 64 128 256), losses := [] }

theorem u497 : Upper (D 2) (R 2) [112,129,258,384,4,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b497
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 390, targets := 16 }], pairs := [(1,4)], upper := (rows 113 131 262 392 24 48 100 228 356), lower := (rows 113 131 262 392 24 48 64 128 256), losses := [] }

theorem u498 : Upper (D 2) (R 2) [112,129,258,384,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b498
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 262 392 24 96 116 180 308), lower := (rows 113 131 262 392 24 96 64 128 256), losses := [] }

theorem u499 : Upper (D 2) (R 2) [112,129,258,384,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b499
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 268, targets := 128 }], pairs := [(2,7)], upper := (rows 113 131 276 296 18 160 76 204 332), lower := (rows 113 131 276 296 18 160 64 128 256), losses := [] }

theorem u500 : Upper (D 2) (R 2) [112,129,272,288,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b500
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b501 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 276 296 20 160 74 202 330), lower := (rows 113 131 276 296 20 160 64 128 256), losses := [] }

theorem u501 : Upper (D 2) (R 2) [112,129,272,288,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b501
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b502 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 276 296 24 160 70 198 326), lower := (rows 113 131 276 296 24 160 64 128 256), losses := [] }

theorem u502 : Upper (D 2) (R 2) [112,129,272,288,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b502
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 131 276 296 80 160 78 142 270), lower := (rows 113 131 276 296 80 160 64 128 256), losses := [] }

theorem u503 : Upper (D 2) (R 2) [112,129,272,288,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b503
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 276 296 144 33 74 202 330), lower := (rows 113 134 276 296 144 33 64 128 256), losses := [] }

theorem u504 : Upper (D 2) (R 2) [112,132,272,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b504
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 268, targets := 128 }], pairs := [(2,7)], upper := (rows 113 134 276 296 144 34 73 201 329), lower := (rows 113 134 276 296 144 34 64 128 256), losses := [] }

theorem u505 : Upper (D 2) (R 2) [112,132,272,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b505
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 276 296 144 40 67 195 323), lower := (rows 113 134 276 296 144 40 64 128 256), losses := [] }

theorem u506 : Upper (D 2) (R 2) [112,132,272,288,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b506
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 134 276 296 144 96 75 139 267), lower := (rows 113 134 276 296 144 96 64 128 256), losses := [] }

theorem u507 : Upper (D 2) (R 2) [112,132,272,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b507
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 364, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 164 328 17 288 78 142 270), lower := (rows 113 146 164 328 17 288 64 128 256), losses := [] }

theorem u508 : Upper (D 2) (R 2) [112,144,160,320,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b508
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 164 328 18 288 77 141 269), lower := (rows 113 146 164 328 18 288 64 128 256), losses := [] }

theorem u509 : Upper (D 2) (R 2) [112,144,160,320,2,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b509
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b510 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 164 328 20 288 75 139 267), lower := (rows 113 146 164 328 20 288 64 128 256), losses := [] }

theorem u510 : Upper (D 2) (R 2) [112,144,160,320,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b510
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b511 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 164 328 24 288 71 135 263), lower := (rows 113 146 164 328 24 288 64 128 256), losses := [] }

theorem u511 : Upper (D 2) (R 2) [112,144,160,320,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b511
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 15 19 52 200 48 480 448 448 448), lower := (rows 15 19 52 200 48 32 64 128 256), losses := [] }

theorem u512 : Upper (D 2) (R 2) [14,17,48,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b512
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 488, targets := 16 },{ cop := 1, region := 420, targets := 64 }], pairs := [(2,6),(3,4)], upper := (rows 15 19 52 200 80 416 480 416 416), lower := (rows 15 19 52 200 80 32 64 128 256), losses := [] }

theorem u513 : Upper (D 2) (R 2) [14,17,48,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b513
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r514 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u514 : Upper (D 2) (R 2) [14,17,48,192,256] 13 := by
  apply FastRouting.sound _ _ [14,17,48,192,256] 13 (by decide) (choices 1) [64,256] r514 c514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u77
  · exact u78

def b515 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 424, targets := 64 }], pairs := [(1,5),(3,6)], upper := (rows 15 19 100 168 80 432 464 400 400), lower := (rows 15 19 100 168 80 32 64 128 256), losses := [] }

theorem u515 : Upper (D 2) (R 2) [14,17,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b515
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m516_128 : Upper (D 2) (R 2) [14,17,96,160,256,128] 13 :=
  permutation_upper _ _ _ [14,17,96,160,256,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u80

def r516 : Route 9 := (fun mask => (mask,id))

def c516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u516 : Upper (D 2) (R 2) [14,17,96,160,256] 13 := by
  apply FastRouting.sound _ _ [14,17,96,160,256] 13 (by decide) (choices 1) [16,64,128,256] r516 c516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u79
  · exact u80
  · exact m516_128
  · exact u81

def b517 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(1,6),(3,5)], upper := (rows 15 19 100 392 48 496 464 464 464), lower := (rows 15 19 100 392 48 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 52 32 0 128 256), good := (rows 31 19 52 392 48 48 0 128 256) }] }

theorem u517 : Upper (D 2) (R 2) [14,17,96,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b517
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 392 17 480 480 480 480), lower := (rows 15 50 84 392 17 32 64 128 256), losses := [] }

theorem u518 : Upper (D 2) (R 2) [14,48,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b518
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 15 50 84 392 48 481 449 449 449), lower := (rows 15 50 84 392 48 32 64 128 256), losses := [] }

theorem u519 : Upper (D 2) (R 2) [14,48,80,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b519
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r520 : Route 9 := (fun mask => (mask,id))

def c520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u520 : Upper (D 2) (R 2) [14,48,80,384,128] 13 := by
  apply FastRouting.sound _ _ [14,48,80,384,128] 13 (by decide) (choices 1) [1,64,256] r520 c520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u82
  · exact u83
  · exact u84

def b521 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 27, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 23 11 100 56 80 416 448 384 384), lower := (rows 23 11 100 56 80 32 64 128 256), losses := [] }

theorem u521 : Upper (D 2) (R 2) [22,9,96,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b521
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r522 : Route 9 := (fun mask => (mask,id))

def c522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u522 : Upper (D 2) (R 2) [22,9,96,48,128] 13 := by
  apply FastRouting.sound _ _ [22,9,96,48,128] 13 (by decide) (choices 1) [64,128,256] r522 c522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u85
  · exact u86
  · exact u87

def b523 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 23 11 100 152 48 480 448 448 448), lower := (rows 23 11 100 152 48 32 64 128 256), losses := [] }

theorem u523 : Upper (D 2) (R 2) [22,9,96,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b523
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 23 11 100 152 144 352 352 480 352), lower := (rows 23 11 100 152 144 32 64 128 256), losses := [] }

theorem u524 : Upper (D 2) (R 2) [22,9,96,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b524
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r525 : Route 9 := (fun mask => (mask,id))

def c525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u525 : Upper (D 2) (R 2) [22,9,96,144,256] 13 := by
  apply FastRouting.sound _ _ [22,9,96,144,256] 13 (by decide) (choices 1) [64,128,256] r525 c525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u88
  · exact u89
  · exact u90

def b526 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 23 11 100 168 80 432 464 400 400), lower := (rows 23 11 100 168 80 32 64 128 256), losses := [] }

theorem u526 : Upper (D 2) (R 2) [22,9,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b526
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r527 : Route 9 := (fun mask => (mask,id))

def c527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u527 : Upper (D 2) (R 2) [22,9,96,160,128] 13 := by
  apply FastRouting.sound _ _ [22,9,96,160,128] 13 (by decide) (choices 1) [16,64,256] r527 c527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u91
  · exact u92
  · exact u93

def r528 : Route 9 := (fun mask => (mask,id))

def c528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u528 : Upper (D 2) (R 2) [22,9,96,160,256] 13 := by
  apply FastRouting.sound _ _ [22,9,96,160,256] 13 (by decide) (choices 1) [16,64,128,256] r528 c528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u94
  · exact u95
  · exact u96
  · exact u97

def b529 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 23 11 100 392 48 496 464 464 464), lower := (rows 23 11 100 392 48 32 64 128 256), losses := [] }

theorem u529 : Upper (D 2) (R 2) [22,9,96,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b529
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r530 : Route 9 := (fun mask => (mask,id))

def c530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u530 : Upper (D 2) (R 2) [22,9,96,384,128] 13 := by
  apply FastRouting.sound _ _ [22,9,96,384,128] 13 (by decide) (choices 1) [16,64,256] r530 c530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u98
  · exact u99
  · exact u100

def b531 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(3,5)], upper := (rows 23 35 44 200 80 432 464 400 400), lower := (rows 23 35 44 200 80 32 64 128 256), losses := [] }

theorem u531 : Upper (D 2) (R 2) [22,33,40,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b531
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r532 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u532 : Upper (D 2) (R 2) [22,33,40,192,256] 13 := by
  apply FastRouting.sound _ _ [22,33,40,192,256] 13 (by decide) (choices 1) [16,64,256] r532 c532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u101
  · exact u102
  · exact u103

def b533 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 23 35 76 168 80 432 464 400 400), lower := (rows 23 35 76 168 80 32 64 128 256), losses := [] }

theorem u533 : Upper (D 2) (R 2) [22,33,72,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b533
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b534 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 354, targets := 128 },{ cop := 3, region := 340, targets := 32 }], pairs := [(1,7),(2,5)], upper := (rows 23 35 76 168 144 368 336 464 336), lower := (rows 23 35 76 168 144 32 64 128 256), losses := [] }

theorem u534 : Upper (D 2) (R 2) [22,33,72,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b534
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r535 : Route 9 := (fun mask => (mask,id))

def c535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u535 : Upper (D 2) (R 2) [22,33,72,160,256] 13 := by
  apply FastRouting.sound _ _ [22,33,72,160,256] 13 (by decide) (choices 1) [16,64,128,256] r535 c535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u104
  · exact u105
  · exact u106
  · exact u107

def b536 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 23 35 76 392 48 496 464 464 464), lower := (rows 23 35 76 392 48 32 64 128 256), losses := [] }

theorem u536 : Upper (D 2) (R 2) [22,33,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b536
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 23 35 76 392 80 432 496 432 432), lower := (rows 23 35 76 392 80 32 64 128 256), losses := [] }

theorem u537 : Upper (D 2) (R 2) [22,33,72,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b537
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r538 : Route 9 := (fun mask => (mask,id))

def c538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u538 : Upper (D 2) (R 2) [22,33,72,384,128] 13 := by
  apply FastRouting.sound _ _ [22,33,72,384,128] 13 (by decide) (choices 1) [16,64,256] r538 c538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u108
  · exact u109
  · exact u110

def b539 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 100 200 24 432 464 400 400), lower := (rows 23 35 100 200 24 32 64 128 256), losses := [] }

theorem u539 : Upper (D 2) (R 2) [22,33,96,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b539
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P02
