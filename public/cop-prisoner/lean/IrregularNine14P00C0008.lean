import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0000
import IrregularNine14P00C0001

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b480 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 76 137 17 48 228 164 420), lower := (rows 51 322 76 137 17 48 64 128 256), losses := [] }

theorem u480 : Upper (D 0) (R 0) [50,320,72,129,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b480
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r481 : Route 9 := (fun mask => (mask,id))

def c481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u481 : Upper (D 0) (R 0) [50,320,72,129,1,128] 13 := by
  apply FastRouting.sound _ _ [50,320,72,129,1,128] 13 (by decide) (choices 1) [4,16,32] r481 c481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u49
  · exact u50
  · exact u51

def b482 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 322 76 137 20 160 113 177 305), lower := (rows 51 322 76 137 20 160 64 128 256), losses := [] }

theorem u482 : Upper (D 0) (R 0) [50,320,72,129,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b482
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 76 137 48 160 85 149 277), lower := (rows 51 322 76 137 48 160 64 128 256), losses := [] }

theorem u483 : Upper (D 0) (R 0) [50,320,72,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b483
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 76 152 17 33 228 164 420), lower := (rows 51 322 76 152 17 33 64 128 256), losses := [] }

theorem u484 : Upper (D 0) (R 0) [50,320,72,144,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b484
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b485 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 322 76 152 17 36 225 161 417), lower := (rows 51 322 76 152 17 36 64 128 256), losses := [] }

theorem u485 : Upper (D 0) (R 0) [50,320,72,144,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b485
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r486 : Route 9 := (fun mask => (mask,id))

def c486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u486 : Upper (D 0) (R 0) [50,320,72,144,1,128] 13 := by
  apply FastRouting.sound _ _ [50,320,72,144,1,128] 13 (by decide) (choices 1) [1,4,32] r486 c486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u52
  · exact u53
  · exact u54

def b487 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 51 322 84 137 17 36 232 168 424), lower := (rows 51 322 84 137 17 36 64 128 256), losses := [] }

theorem u487 : Upper (D 0) (R 0) [50,320,80,129,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b487
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b488 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 51 322 84 137 17 40 228 164 420), lower := (rows 51 322 84 137 17 40 64 128 256), losses := [] }

theorem u488 : Upper (D 0) (R 0) [50,320,80,129,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b488
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r489 : Route 9 := (fun mask => (mask,id))

def c489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u489 : Upper (D 0) (R 0) [50,320,80,129,1,128] 13 := by
  apply FastRouting.sound _ _ [50,320,80,129,1,128] 13 (by decide) (choices 1) [4,8,32] r489 c489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u55
  · exact u56
  · exact u57

def r490 : Route 9 := (fun mask => (mask,id))

def c490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u490 : Upper (D 0) (R 0) [50,320,80,129,128,1] 13 := by
  apply FastRouting.sound _ _ [50,320,80,129,128,1] 13 (by decide) (choices 1) [4,8,32] r490 c490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u58
  · exact u59
  · exact u60

def b491 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 51 322 84 137 144 36 105 169 297), lower := (rows 51 322 84 137 144 36 64 128 256), losses := [] }

theorem u491 : Upper (D 0) (R 0) [50,320,80,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b491
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 322 84 137 144 40 101 165 293), lower := (rows 51 322 84 137 144 40 64 128 256), losses := [] }

theorem u492 : Upper (D 0) (R 0) [50,320,80,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b492
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 84 140 17 33 232 168 424), lower := (rows 51 322 84 140 17 33 64 128 256), losses := [] }

theorem u493 : Upper (D 0) (R 0) [50,320,80,132,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b493
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 322 84 140 17 40 225 161 417), lower := (rows 51 322 84 140 17 40 64 128 256), losses := [] }

theorem u494 : Upper (D 0) (R 0) [50,320,80,132,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b494
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r495 : Route 9 := (fun mask => (mask,id))

def c495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u495 : Upper (D 0) (R 0) [50,320,80,132,1,128] 13 := by
  apply FastRouting.sound _ _ [50,320,80,132,1,128] 13 (by decide) (choices 1) [1,8,32] r495 c495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u61
  · exact u62
  · exact u63

def r496 : Route 9 := (fun mask => (mask,id))

def c496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u496 : Upper (D 0) (R 0) [50,320,80,132,128,1] 13 := by
  apply FastRouting.sound _ _ [50,320,80,132,128,1] 13 (by decide) (choices 1) [1,8,32] r496 c496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u64
  · exact u65
  · exact u66

def b497 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 51 322 84 140 144 40 97 161 289), lower := (rows 51 322 84 140 144 40 64 128 256), losses := [] }

theorem u497 : Upper (D 0) (R 0) [50,320,80,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b497
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 84 168 17 33 204 140 396), lower := (rows 51 322 84 168 17 33 64 128 256), losses := [] }

theorem u498 : Upper (D 0) (R 0) [50,320,80,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b498
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 51 322 84 168 17 36 201 137 393), lower := (rows 51 322 84 168 17 36 64 128 256), losses := [] }

theorem u499 : Upper (D 0) (R 0) [50,320,80,160,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b499
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 322 84 168 17 40 197 133 389), lower := (rows 51 322 84 168 17 40 64 128 256), losses := [] }

theorem u500 : Upper (D 0) (R 0) [50,320,80,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b500
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b501 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 84 168 17 160 77 141 269), lower := (rows 51 322 84 168 17 160 64 128 256), losses := [] }

theorem u501 : Upper (D 0) (R 0) [50,320,80,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b501
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r502 : Route 9 := (fun mask => (mask,id))

def c502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u502 : Upper (D 0) (R 0) [50,320,80,160,128,1] 13 := by
  apply FastRouting.sound _ _ [50,320,80,160,128,1] 13 (by decide) (choices 1) [1,4,8] r502 c502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u67
  · exact u68
  · exact u69

def b503 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 51 322 84 168 144 36 73 137 265), lower := (rows 51 322 84 168 144 36 64 128 256), losses := [] }

theorem u503 : Upper (D 0) (R 0) [50,320,80,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b503
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 51 322 84 168 144 40 69 133 261), lower := (rows 51 322 84 168 144 40 64 128 256), losses := [] }

theorem u504 : Upper (D 0) (R 0) [50,320,80,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b504
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 51 322 133 200 17 36 120 184 312), lower := (rows 51 322 133 200 17 36 64 128 256), losses := [] }

theorem u505 : Upper (D 0) (R 0) [50,320,129,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b505
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 51 322 133 200 17 40 116 180 308), lower := (rows 51 322 133 200 17 40 64 128 256), losses := [] }

theorem u506 : Upper (D 0) (R 0) [50,320,129,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b506
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 133 200 17 48 108 172 300), lower := (rows 51 322 133 200 17 48 64 128 256), losses := [] }

theorem u507 : Upper (D 0) (R 0) [50,320,129,192,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b507
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 148 168 17 33 76 204 332), lower := (rows 51 322 148 168 17 33 64 128 256), losses := [] }

theorem u508 : Upper (D 0) (R 0) [50,320,144,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b508
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 51 322 148 168 17 36 73 201 329), lower := (rows 51 322 148 168 17 36 64 128 256), losses := [] }

theorem u509 : Upper (D 0) (R 0) [50,320,144,160,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b509
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b510 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 51 322 148 168 17 40 69 197 325), lower := (rows 51 322 148 168 17 40 64 128 256), losses := [] }

theorem u510 : Upper (D 0) (R 0) [50,320,144,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b510
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b511 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 148 168 17 96 77 141 269), lower := (rows 51 322 148 168 17 96 64 128 256), losses := [] }

theorem u511 : Upper (D 0) (R 0) [50,320,144,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b511
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 148 200 17 33 108 172 300), lower := (rows 51 322 148 200 17 33 64 128 256), losses := [] }

theorem u512 : Upper (D 0) (R 0) [50,320,144,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b512
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 51 322 148 200 17 36 105 169 297), lower := (rows 51 322 148 200 17 36 64 128 256), losses := [] }

theorem u513 : Upper (D 0) (R 0) [50,320,144,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b513
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b514 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 322 148 200 17 40 101 165 293), lower := (rows 51 322 148 200 17 40 64 128 256), losses := [] }

theorem u514 : Upper (D 0) (R 0) [50,320,144,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b514
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b515 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 392, targets := 1 }], pairs := [(3,0)], upper := (rows 113 7 14 280 144 33 224 224 480), lower := (rows 113 7 14 280 144 33 64 128 256), losses := [] }

theorem u515 : Upper (D 0) (R 0) [112,5,10,272,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b515
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b516 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 14 280 144 96 225 161 417), lower := (rows 113 7 14 280 144 96 64 128 256), losses := [] }

theorem u516 : Upper (D 0) (R 0) [112,5,10,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b516
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b517 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 7 14 280 144 160 97 225 353), lower := (rows 113 7 14 280 144 160 64 128 256), losses := [] }

theorem u517 : Upper (D 0) (R 0) [112,5,10,272,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b517
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 113 7 140 265 18 160 112 240 368), lower := (rows 113 7 140 265 18 160 64 128 256), losses := [] }

theorem u518 : Upper (D 0) (R 0) [112,5,136,257,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b518
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 140 265 48 160 82 210 338), lower := (rows 113 7 140 265 48 160 64 128 256), losses := [] }

theorem u519 : Upper (D 0) (R 0) [112,5,136,257,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b519
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b520 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 140 265 80 160 114 178 306), lower := (rows 113 7 140 265 80 160 64 128 256), losses := [] }

theorem u520 : Upper (D 0) (R 0) [112,5,136,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b520
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b521 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 113 7 140 280 17 34 224 224 480), lower := (rows 113 7 140 280 17 34 64 128 256), losses := [] }

theorem u521 : Upper (D 0) (R 0) [112,5,136,272,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b521
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b522 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 140 280 17 96 226 162 418), lower := (rows 113 7 140 280 17 96 64 128 256), losses := [] }

theorem u522 : Upper (D 0) (R 0) [112,5,136,272,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b522
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m523_2 : Upper (D 0) (R 0) [112,5,136,272,1,128,2] 13 :=
  permutation_upper _ _ _ [112,5,136,272,1,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u70

theorem m523_32 : Upper (D 0) (R 0) [112,5,136,272,1,128,32] 13 :=
  permutation_upper _ _ _ [112,5,136,272,1,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u71

def r523 : Route 9 := (fun mask => (mask,id))

def c523 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u523 : Upper (D 0) (R 0) [112,5,136,272,1,128] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272,1,128] 13 (by decide) (choices 1) [2,32] r523 c523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m523_2
  · exact m523_32

def r524 : Route 9 := (fun mask => (mask,id))

def c524 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u524 : Upper (D 0) (R 0) [112,5,136,272,128,1] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272,128,1] 13 (by decide) (choices 1) [2,32] r524 c524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u72
  · exact u73

def b525 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 113 7 140 280 144 34 97 225 353), lower := (rows 113 7 140 280 144 34 64 128 256), losses := [] }

theorem u525 : Upper (D 0) (R 0) [112,5,136,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b525
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b526 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 140 280 144 96 99 163 291), lower := (rows 113 7 140 280 144 96 64 128 256), losses := [] }

theorem u526 : Upper (D 0) (R 0) [112,5,136,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b526
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 113 7 262 137 24 160 112 240 368), lower := (rows 113 7 262 137 24 160 64 128 256), losses := [] }

theorem u527 : Upper (D 0) (R 0) [112,5,258,129,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b527
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 262 137 48 160 88 216 344), lower := (rows 113 7 262 137 48 160 64 128 256), losses := [] }

theorem u528 : Upper (D 0) (R 0) [112,5,258,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b528
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 262 137 80 160 120 184 312), lower := (rows 113 7 262 137 80 160 64 128 256), losses := [] }

theorem u529 : Upper (D 0) (R 0) [112,5,258,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b529
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 113 7 268 137 18 160 112 240 368), lower := (rows 113 7 268 137 18 160 64 128 256), losses := [] }

theorem u530 : Upper (D 0) (R 0) [112,5,264,129,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b530
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b531 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 268 137 48 160 82 210 338), lower := (rows 113 7 268 137 48 160 64 128 256), losses := [] }

theorem u531 : Upper (D 0) (R 0) [112,5,264,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b531
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b532 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 268 137 80 160 114 178 306), lower := (rows 113 7 268 137 80 160 64 128 256), losses := [] }

theorem u532 : Upper (D 0) (R 0) [112,5,264,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b532
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b533 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 113 7 268 152 17 34 224 224 480), lower := (rows 113 7 268 152 17 34 64 128 256), losses := [] }

theorem u533 : Upper (D 0) (R 0) [112,5,264,144,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b533
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b534 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 268 152 17 96 226 162 418), lower := (rows 113 7 268 152 17 96 64 128 256), losses := [] }

theorem u534 : Upper (D 0) (R 0) [112,5,264,144,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b534
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m535_2 : Upper (D 0) (R 0) [112,5,264,144,1,128,2] 13 :=
  permutation_upper _ _ _ [112,5,264,144,1,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u74

theorem m535_32 : Upper (D 0) (R 0) [112,5,264,144,1,128,32] 13 :=
  permutation_upper _ _ _ [112,5,264,144,1,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u75

def r535 : Route 9 := (fun mask => (mask,id))

def c535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u535 : Upper (D 0) (R 0) [112,5,264,144,1,128] 13 := by
  apply FastRouting.sound _ _ [112,5,264,144,1,128] 13 (by decide) (choices 1) [2,32] r535 c535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m535_2
  · exact m535_32

def b536 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 113 7 388 152 17 34 104 232 360), lower := (rows 113 7 388 152 17 34 64 128 256), losses := [] }

theorem u536 : Upper (D 0) (R 0) [112,5,384,144,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b536
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 7 388 152 17 40 98 226 354), lower := (rows 113 7 388 152 17 40 64 128 256), losses := [] }

theorem u537 : Upper (D 0) (R 0) [112,5,384,144,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b537
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b538 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 388 152 17 96 106 170 298), lower := (rows 113 7 388 152 17 96 64 128 256), losses := [] }

theorem u538 : Upper (D 0) (R 0) [112,5,384,144,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b538
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 113 14 133 265 18 160 112 240 368), lower := (rows 113 14 133 265 18 160 64 128 256), losses := [] }

theorem u539 : Upper (D 0) (R 0) [112,12,129,257,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b539
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P00
