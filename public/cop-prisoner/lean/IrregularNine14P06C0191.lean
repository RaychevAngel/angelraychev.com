import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0030
import IrregularNine14P06C0031

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11460 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 19 100 41 208 288 70 134 262), lower := (rows 11 19 100 41 208 288 64 128 256), losses := [] }

theorem u11460 : Upper (D 6) (R 6) [10,17,96,33,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11460
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11461 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 100 41 400 34 68 196 324), lower := (rows 11 19 100 41 400 34 64 128 256), losses := [] }

theorem u11461 : Upper (D 6) (R 6) [10,17,96,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11461
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11462 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 41 400 36 70 198 326), lower := (rows 11 19 100 41 400 36 64 128 256), losses := [] }

theorem u11462 : Upper (D 6) (R 6) [10,17,96,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11462
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11463 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 41 400 96 70 134 262), lower := (rows 11 19 100 41 400 96 64 128 256), losses := [] }

theorem u11463 : Upper (D 6) (R 6) [10,17,96,33,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11463
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11464 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 137 276 34 100 228 356), lower := (rows 11 19 100 137 276 34 64 128 256), losses := [] }

theorem u11464 : Upper (D 6) (R 6) [10,17,96,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11464
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11465 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 137 276 36 98 226 354), lower := (rows 11 19 100 137 276 36 64 128 256), losses := [] }

theorem u11465 : Upper (D 6) (R 6) [10,17,96,129,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11465
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11466 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 137 276 96 102 166 294), lower := (rows 11 19 100 137 276 96 64 128 256), losses := [] }

theorem u11466 : Upper (D 6) (R 6) [10,17,96,129,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11466
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11467 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 137 304 34 68 196 324), lower := (rows 11 19 100 137 304 34 64 128 256), losses := [] }

theorem u11467 : Upper (D 6) (R 6) [10,17,96,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11467
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11468 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 137 304 36 70 198 326), lower := (rows 11 19 100 137 304 36 64 128 256), losses := [] }

theorem u11468 : Upper (D 6) (R 6) [10,17,96,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11468
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11469 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 137 304 96 70 134 262), lower := (rows 11 19 100 137 304 96 64 128 256), losses := [] }

theorem u11469 : Upper (D 6) (R 6) [10,17,96,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11469
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11470 : Route 9 := (fun mask => (mask,id))

def c11470 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11470 : Upper (D 6) (R 6) [10,17,96,132,260,1] 13 := by
  apply FastRouting.sound _ _ [10,17,96,132,260,1] 13 (by decide) (choices 1) [2,32] r11470 c11470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1842
  · exact u1843

def b11471 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 140 276 96 99 163 291), lower := (rows 11 19 100 140 276 96 64 128 256), losses := [] }

theorem u11471 : Upper (D 6) (R 6) [10,17,96,132,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11471
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11472 : Route 9 := (fun mask => (mask,id))

def c11472 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11472 : Upper (D 6) (R 6) [10,17,96,132,288,1] 13 := by
  apply FastRouting.sound _ _ [10,17,96,132,288,1] 13 (by decide) (choices 1) [2,4] r11472 c11472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1844
  · exact u1845

def r11473 : Route 9 := (fun mask => (mask,id))

def c11473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11473 : Upper (D 6) (R 6) [10,17,96,132,288,2] 13 := by
  apply FastRouting.sound _ _ [10,17,96,132,288,2] 13 (by decide) (choices 1) [1,4] r11473 c11473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1846
  · exact u1847

def r11474 : Route 9 := (fun mask => (mask,id))

def c11474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11474 : Upper (D 6) (R 6) [10,17,96,132,288,4] 13 := by
  apply FastRouting.sound _ _ [10,17,96,132,288,4] 13 (by decide) (choices 1) [1,2] r11474 c11474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1848
  · exact u1849

def b11475 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 140 304 96 71 135 263), lower := (rows 11 19 100 140 304 96 64 128 256), losses := [] }

theorem u11475 : Upper (D 6) (R 6) [10,17,96,132,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11475
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11476 : Route 9 := (fun mask => (mask,id))

def c11476 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11476 : Upper (D 6) (R 6) [10,17,96,160,320,1] 13 := by
  apply FastRouting.sound _ _ [10,17,96,160,320,1] 13 (by decide) (choices 1) [2,4] r11476 c11476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1850
  · exact u1851

def r11477 : Route 9 := (fun mask => (mask,id))

def c11477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11477 : Upper (D 6) (R 6) [10,17,96,160,320,2] 13 := by
  apply FastRouting.sound _ _ [10,17,96,160,320,2] 13 (by decide) (choices 1) [1,4] r11477 c11477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1852
  · exact u1853

theorem m11478_1 : Upper (D 6) (R 6) [10,17,96,160,320,4,1] 13 :=
  permutation_upper _ _ _ [10,17,96,160,320,2,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1853

theorem m11478_2 : Upper (D 6) (R 6) [10,17,96,160,320,4,2] 13 :=
  permutation_upper _ _ _ [10,17,96,160,320,1,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1851

def r11478 : Route 9 := (fun mask => (mask,id))

def c11478 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11478 : Upper (D 6) (R 6) [10,17,96,160,320,4] 13 := by
  apply FastRouting.sound _ _ [10,17,96,160,320,4] 13 (by decide) (choices 1) [1,2,4] r11478 c11478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m11478_1
  · exact m11478_2
  · exact u1854

def b11479 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 133 44 84 34 352 480 352), lower := (rows 11 19 133 44 84 34 64 128 256), losses := [] }

theorem u11479 : Upper (D 6) (R 6) [10,17,129,36,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11479
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11480 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 133 44 84 96 354 418 290), lower := (rows 11 19 133 44 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 119 67 131 259), good := (rows 490 506 508 60 124 96 96 128 256) }] }

theorem u11480 : Upper (D 6) (R 6) [10,17,129,36,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11480
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11481 : PairBound 9 := { available := 98, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 19 133 44 84 288 98 226 354), lower := (rows 11 19 133 44 84 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 295 67 131 259), good := (rows 490 506 508 60 124 288 64 128 288) }] }

theorem u11481 : Upper (D 6) (R 6) [10,17,129,36,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11481
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11482 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 3, region := 336, targets := 1 }], pairs := [(2,1),(2,5),(4,0)], upper := (rows 11 19 133 44 112 34 324 452 324), lower := (rows 11 19 133 44 112 34 64 128 256), losses := [] }

theorem u11482 : Upper (D 6) (R 6) [10,17,129,36,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11482
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11483 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 133 44 112 36 322 450 322), lower := (rows 11 19 133 44 112 36 64 128 256), losses := [] }

theorem u11483 : Upper (D 6) (R 6) [10,17,129,36,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11483
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11484 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 133 44 112 96 326 390 262), lower := (rows 11 19 133 44 112 96 64 128 256), losses := [] }

theorem u11484 : Upper (D 6) (R 6) [10,17,129,36,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11484
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11485 : Route 9 := (fun mask => (mask,id))

def c11485 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11485 : Upper (D 6) (R 6) [10,17,129,36,96,256] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36,96,256] 13 (by decide) (choices 1) [2,4] r11485 c11485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1855
  · exact u1856

def b11486 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 133 44 276 34 96 224 352), lower := (rows 11 19 133 44 276 34 64 128 256), losses := [] }

theorem u11486 : Upper (D 6) (R 6) [10,17,129,36,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11486
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11487 : Route 9 := (fun mask => (mask,id))

def c11487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11487 : Upper (D 6) (R 6) [10,17,129,36,260,64] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36,260,64] 13 (by decide) (choices 1) [2,32] r11487 c11487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1857
  · exact u1858

def b11488 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 3, region := 336, targets := 1 }], pairs := [(2,1),(2,5),(4,0)], upper := (rows 11 19 133 44 304 34 68 196 324), lower := (rows 11 19 133 44 304 34 64 128 256), losses := [] }

theorem u11488 : Upper (D 6) (R 6) [10,17,129,36,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11488
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11489 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 133 44 304 36 66 194 322), lower := (rows 11 19 133 44 304 36 64 128 256), losses := [] }

theorem u11489 : Upper (D 6) (R 6) [10,17,129,36,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11489
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11490 : Route 9 := (fun mask => (mask,id))

def c11490 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11490 : Upper (D 6) (R 6) [10,17,129,36,288,64] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36,288,64] 13 (by decide) (choices 1) [2,4] r11490 c11490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1859
  · exact u1860

def b11491 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 336, targets := 3 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 11 19 133 44 336 34 100 228 356), lower := (rows 11 19 133 44 336 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 29 35 76 140 268), good := (rows 506 50 508 508 336 34 64 128 256) }] }

theorem u11491 : Upper (D 6) (R 6) [10,17,129,36,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11491
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11492 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 133 44 336 36 98 226 354), lower := (rows 11 19 133 44 336 36 64 128 256), losses := [] }

theorem u11492 : Upper (D 6) (R 6) [10,17,129,36,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11492
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11493 : Route 9 := (fun mask => (mask,id))

def c11493 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11493 : Upper (D 6) (R 6) [10,17,129,36,320,64] 13 := by
  apply FastRouting.sound _ _ [10,17,129,36,320,64] 13 (by decide) (choices 1) [2,4,32] r11493 c11493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1861
  · exact u1862
  · exact u1863

def b11494 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 50, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 11 19 133 104 52 34 324 452 324), lower := (rows 11 19 133 104 52 34 64 128 256), losses := [] }

theorem u11494 : Upper (D 6) (R 6) [10,17,129,96,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11494
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11495 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 133 104 52 36 322 450 322), lower := (rows 11 19 133 104 52 36 64 128 256), losses := [] }

theorem u11495 : Upper (D 6) (R 6) [10,17,129,96,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11495
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11496 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 133 104 52 96 326 390 262), lower := (rows 11 19 133 104 52 96 64 128 256), losses := [] }

theorem u11496 : Upper (D 6) (R 6) [10,17,129,96,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11496
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11497 : Route 9 := (fun mask => (mask,id))

def c11497 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11497 : Upper (D 6) (R 6) [10,17,129,96,36,256] 13 := by
  apply FastRouting.sound _ _ [10,17,129,96,36,256] 13 (by decide) (choices 1) [2,4] r11497 c11497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1864
  · exact u1865

def r11498 : Route 9 := (fun mask => (mask,id))

def c11498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11498 : Upper (D 6) (R 6) [10,17,129,96,260,2] 13 := by
  apply FastRouting.sound _ _ [10,17,129,96,260,2] 13 (by decide) (choices 1) [4,32] r11498 c11498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1866
  · exact u1867

theorem m11499_2 : Upper (D 6) (R 6) [10,17,129,96,260,4,2] 13 :=
  permutation_upper _ _ _ [10,17,129,96,260,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1866

def r11499 : Route 9 := (fun mask => (mask,id))

def c11499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11499 : Upper (D 6) (R 6) [10,17,129,96,260,4] 13 := by
  apply FastRouting.sound _ _ [10,17,129,96,260,4] 13 (by decide) (choices 1) [2,32] r11499 c11499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11499_2
  · exact u1868

def b11500 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 133 104 276 96 102 166 294), lower := (rows 11 19 133 104 276 96 64 128 256), losses := [] }

theorem u11500 : Upper (D 6) (R 6) [10,17,129,96,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11500
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11501 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 34 }], pairs := [(2,1),(2,5),(3,0)], upper := (rows 11 19 133 104 304 34 68 196 324), lower := (rows 11 19 133 104 304 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 68 132 260), good := (rows 42 50 508 104 304 34 64 128 256) }] }

theorem u11501 : Upper (D 6) (R 6) [10,17,129,96,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11501
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11502 : Route 9 := (fun mask => (mask,id))

def c11502 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11502 : Upper (D 6) (R 6) [10,17,129,96,288,4] 13 := by
  apply FastRouting.sound _ _ [10,17,129,96,288,4] 13 (by decide) (choices 1) [2,4] r11502 c11502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1869
  · exact u1870

def b11503 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 133 104 304 96 70 134 262), lower := (rows 11 19 133 104 304 96 64 128 256), losses := [] }

theorem u11503 : Upper (D 6) (R 6) [10,17,129,96,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11503
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11504 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 19 133 268 52 34 96 224 352), lower := (rows 11 19 133 268 52 34 64 128 256), losses := [] }

theorem u11504 : Upper (D 6) (R 6) [10,17,129,260,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11504
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11505 : Route 9 := (fun mask => (mask,id))

def c11505 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11505 : Upper (D 6) (R 6) [10,17,129,260,36,64] 13 := by
  apply FastRouting.sound _ _ [10,17,129,260,36,64] 13 (by decide) (choices 1) [2,32] r11505 c11505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1871
  · exact u1872

def r11506 : Route 9 := (fun mask => (mask,id))

def c11506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11506 : Upper (D 6) (R 6) [10,17,129,260,96,2] 13 := by
  apply FastRouting.sound _ _ [10,17,129,260,96,2] 13 (by decide) (choices 1) [4,32] r11506 c11506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1873
  · exact u1874

theorem m11507_2 : Upper (D 6) (R 6) [10,17,129,260,96,4,2] 13 :=
  permutation_upper _ _ _ [10,17,129,260,96,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1873

def r11507 : Route 9 := (fun mask => (mask,id))

def c11507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11507 : Upper (D 6) (R 6) [10,17,129,260,96,4] 13 := by
  apply FastRouting.sound _ _ [10,17,129,260,96,4] 13 (by decide) (choices 1) [2,32] r11507 c11507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11507_2
  · exact u1875

def b11508 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 133 268 112 96 102 166 294), lower := (rows 11 19 133 268 112 96 64 128 256), losses := [] }

theorem u11508 : Upper (D 6) (R 6) [10,17,129,260,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11508
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11509 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 50, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 11 19 133 296 52 34 68 196 324), lower := (rows 11 19 133 296 52 34 64 128 256), losses := [] }

theorem u11509 : Upper (D 6) (R 6) [10,17,129,288,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11509
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11510 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 133 296 52 36 66 194 322), lower := (rows 11 19 133 296 52 36 64 128 256), losses := [] }

theorem u11510 : Upper (D 6) (R 6) [10,17,129,288,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11510
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11511 : Route 9 := (fun mask => (mask,id))

def c11511 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11511 : Upper (D 6) (R 6) [10,17,129,288,36,64] 13 := by
  apply FastRouting.sound _ _ [10,17,129,288,36,64] 13 (by decide) (choices 1) [2,4] r11511 c11511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1876
  · exact u1877

def r11512 : Route 9 := (fun mask => (mask,id))

def c11512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11512 : Upper (D 6) (R 6) [10,17,129,288,68,2] 13 := by
  apply FastRouting.sound _ _ [10,17,129,288,68,2] 13 (by decide) (choices 1) [4,32] r11512 c11512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1878
  · exact u1879

def r11513 : Route 9 := (fun mask => (mask,id))

def c11513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11513 : Upper (D 6) (R 6) [10,17,129,288,68,4] 13 := by
  apply FastRouting.sound _ _ [10,17,129,288,68,4] 13 (by decide) (choices 1) [2,32] r11513 c11513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1880
  · exact u1881

def r11514 : Route 9 := (fun mask => (mask,id))

def c11514 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11514 : Upper (D 6) (R 6) [10,17,129,288,68,64] 13 := by
  apply FastRouting.sound _ _ [10,17,129,288,68,64] 13 (by decide) (choices 1) [2,4,32] r11514 c11514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1882
  · exact u1883
  · exact u1884

def b11515 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 34 }], pairs := [(2,1),(2,5),(3,0)], upper := (rows 11 19 133 296 112 34 68 196 324), lower := (rows 11 19 133 296 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 68 132 260), good := (rows 42 50 508 296 112 34 64 128 256) }] }

theorem u11515 : Upper (D 6) (R 6) [10,17,129,288,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11515
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11516 : Route 9 := (fun mask => (mask,id))

def c11516 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11516 : Upper (D 6) (R 6) [10,17,129,288,96,4] 13 := by
  apply FastRouting.sound _ _ [10,17,129,288,96,4] 13 (by decide) (choices 1) [2,4] r11516 c11516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1885
  · exact u1886

def b11517 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 133 296 112 96 70 134 262), lower := (rows 11 19 133 296 112 96 64 128 256), losses := [] }

theorem u11517 : Upper (D 6) (R 6) [10,17,129,288,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11517
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11518 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 13 112 34 324 452 324), lower := (rows 11 19 164 13 112 34 64 128 256), losses := [] }

theorem u11518 : Upper (D 6) (R 6) [10,17,160,5,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11518
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11519 : PairBound 9 := { available := 322, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 13 112 36 322 450 322), lower := (rows 11 19 164 13 112 36 64 128 256), losses := [] }

theorem u11519 : Upper (D 6) (R 6) [10,17,160,5,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11519
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11519
end Delivery.IrregularNine14.P06
