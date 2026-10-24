import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0032

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5460 : Route 9 := (fun mask => (mask,id))

def c5460 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5460 : Upper (D 1) (R 1) [304,68,18,129,128] 13 := by
  apply FastRouting.sound _ _ [304,68,18,129,128] 13 (by decide) (choices 1) [2,8,64] r5460 c5460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1930
  · exact u1931
  · exact u1932

def b5461 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 305 70 22 168 17 234 202 202 458), lower := (rows 305 70 22 168 17 32 64 128 256), losses := [] }

theorem u5461 : Upper (D 1) (R 1) [304,68,18,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5461
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5462 : PairBound 9 := { available := 201, camps := [{ cop := 6, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 168 18 233 201 201 457), lower := (rows 305 70 22 168 18 32 64 128 256), losses := [] }

theorem u5462 : Upper (D 1) (R 1) [304,68,18,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5462
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5463 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 70 22 168 24 227 195 195 451), lower := (rows 305 70 22 168 24 32 64 128 256), losses := [] }

theorem u5463 : Upper (D 1) (R 1) [304,68,18,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5463
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5464 : PairBound 9 := { available := 139, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 168 80 171 203 139 395), lower := (rows 305 70 22 168 80 32 64 128 256), losses := [] }

theorem u5464 : Upper (D 1) (R 1) [304,68,18,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5464
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5465 : Route 9 := (fun mask => (mask,id))

def c5465 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5465 : Upper (D 1) (R 1) [304,68,18,160,128] 13 := by
  apply FastRouting.sound _ _ [304,68,18,160,128] 13 (by decide) (choices 1) [1,2,8,64] r5465 c5465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1933
  · exact u1934
  · exact u1935
  · exact u1936

def b5466 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 305 70 22 200 17 170 234 170 426), lower := (rows 305 70 22 200 17 32 64 128 256), losses := [] }

theorem u5466 : Upper (D 1) (R 1) [304,68,18,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5466
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5467 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 200 18 169 233 169 425), lower := (rows 305 70 22 200 18 32 64 128 256), losses := [] }

theorem u5467 : Upper (D 1) (R 1) [304,68,18,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5467
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5468 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 70 22 200 24 163 227 163 419), lower := (rows 305 70 22 200 24 32 64 128 256), losses := [] }

theorem u5468 : Upper (D 1) (R 1) [304,68,18,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5468
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5469 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 200 48 171 203 139 395), lower := (rows 305 70 22 200 48 32 64 128 256), losses := [] }

theorem u5469 : Upper (D 1) (R 1) [304,68,18,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5470 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 200 144 43 107 171 299), lower := (rows 305 70 22 200 144 32 64 128 256), losses := [] }

theorem u5470 : Upper (D 1) (R 1) [304,68,18,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5470
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5471 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 70 28 42 17 226 194 194 450), lower := (rows 305 70 28 42 17 32 64 128 256), losses := [] }

theorem u5471 : Upper (D 1) (R 1) [304,68,24,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5471
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5472 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 70 28 42 18 225 193 193 449), lower := (rows 305 70 28 42 18 32 64 128 256), losses := [] }

theorem u5472 : Upper (D 1) (R 1) [304,68,24,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5472
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5473 : PairBound 9 := { available := 131, camps := [], pairs := [(2,1)], upper := (rows 305 70 28 42 80 163 195 131 387), lower := (rows 305 70 28 42 80 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 82 32 64 128 256), good := (rows 305 84 28 60 80 32 80 128 256) }] }

theorem u5473 : Upper (D 1) (R 1) [304,68,24,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5473
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5474 : Route 9 := (fun mask => (mask,id))

def c5474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5474 : Upper (D 1) (R 1) [304,68,24,34,128] 13 := by
  apply FastRouting.sound _ _ [304,68,24,34,128] 13 (by decide) (choices 1) [1,2,64,128] r5474 c5474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1937
  · exact u1938
  · exact u1939
  · exact u1940

def b5475 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 70 28 138 17 226 226 226 482), lower := (rows 305 70 28 138 17 32 64 128 256), losses := [] }

theorem u5475 : Upper (D 1) (R 1) [304,68,24,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5475
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5476 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 70 28 138 18 225 225 225 481), lower := (rows 305 70 28 138 18 32 64 128 256), losses := [] }

theorem u5476 : Upper (D 1) (R 1) [304,68,24,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5476
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5477 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 28 138 48 227 195 195 451), lower := (rows 305 70 28 138 48 32 64 128 256), losses := [] }

theorem u5477 : Upper (D 1) (R 1) [304,68,24,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5477
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5478 : PairBound 9 := { available := 163, camps := [], pairs := [(2,1)], upper := (rows 305 70 28 138 80 163 227 163 419), lower := (rows 305 70 28 138 80 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 82 32 64 128 256), good := (rows 305 84 28 156 80 32 80 128 256) }] }

theorem u5478 : Upper (D 1) (R 1) [304,68,24,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5478
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5479 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 28 138 144 99 99 227 355), lower := (rows 305 70 28 138 144 32 64 128 256), losses := [] }

theorem u5479 : Upper (D 1) (R 1) [304,68,24,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5479
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5480 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 70 28 168 17 226 194 194 450), lower := (rows 305 70 28 168 17 32 64 128 256), losses := [] }

theorem u5480 : Upper (D 1) (R 1) [304,68,24,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5480
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5481 : Route 9 := (fun mask => (mask,id))

def c5481 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5481 : Upper (D 1) (R 1) [304,68,24,160,2] 13 := by
  apply FastRouting.sound _ _ [304,68,24,160,2] 13 (by decide) (choices 1) [1,2,64,128] r5481 c5481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1941
  · exact u1942
  · exact u1943
  · exact u1944

def r5482 : Route 9 := (fun mask => (mask,id))

def c5482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5482 : Upper (D 1) (R 1) [304,68,24,160,64] 13 := by
  apply FastRouting.sound _ _ [304,68,24,160,64] 13 (by decide) (choices 1) [1,2,128] r5482 c5482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1945
  · exact u1946
  · exact u1947

def b5483 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 28 168 144 99 67 195 323), lower := (rows 305 70 28 168 144 32 64 128 256), losses := [] }

theorem u5483 : Upper (D 1) (R 1) [304,68,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5483
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5484 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 133 26 18 232 232 232 488), lower := (rows 305 70 133 26 18 32 64 128 256), losses := [] }

theorem u5484 : Upper (D 1) (R 1) [304,68,129,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5484
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5485 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 70 133 26 24 226 226 226 482), lower := (rows 305 70 133 26 24 32 64 128 256), losses := [] }

theorem u5485 : Upper (D 1) (R 1) [304,68,129,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5485
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5486 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 133 26 48 234 202 202 458), lower := (rows 305 70 133 26 48 32 64 128 256), losses := [] }

theorem u5486 : Upper (D 1) (R 1) [304,68,129,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5486
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5487 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 133 26 80 170 234 170 426), lower := (rows 305 70 133 26 80 32 64 128 256), losses := [] }

theorem u5487 : Upper (D 1) (R 1) [304,68,129,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5487
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5488 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 133 26 144 106 106 234 362), lower := (rows 305 70 133 26 144 32 64 128 256), losses := [] }

theorem u5488 : Upper (D 1) (R 1) [304,68,129,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5488
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5489 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 133 88 18 170 234 170 426), lower := (rows 305 70 133 88 18 32 64 128 256), losses := [] }

theorem u5489 : Upper (D 1) (R 1) [304,68,129,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5489
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5490 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 133 88 24 162 226 162 418), lower := (rows 305 70 133 88 24 32 64 128 256), losses := [] }

theorem u5490 : Upper (D 1) (R 1) [304,68,129,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5490
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5491 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 133 88 48 170 202 138 394), lower := (rows 305 70 133 88 48 32 64 128 256), losses := [] }

theorem u5491 : Upper (D 1) (R 1) [304,68,129,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5491
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5492 : PairBound 9 := { available := 42, camps := [], pairs := [(3,1)], upper := (rows 305 70 133 88 144 42 106 170 298), lower := (rows 305 70 133 88 144 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 148 32 64 128 256), good := (rows 305 92 149 88 144 32 64 144 256) }] }

theorem u5492 : Upper (D 1) (R 1) [304,68,129,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5492
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5493 : Route 9 := (fun mask => (mask,id))

def c5493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5493 : Upper (D 1) (R 1) [304,68,129,144,2] 13 := by
  apply FastRouting.sound _ _ [304,68,129,144,2] 13 (by decide) (choices 1) [2,8,64] r5493 c5493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1948
  · exact u1949
  · exact u1950

def b5494 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 305 70 133 152 24 98 98 226 354), lower := (rows 305 70 133 152 24 32 64 128 256), losses := [] }

theorem u5494 : Upper (D 1) (R 1) [304,68,129,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5494
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5495 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 133 152 48 106 74 202 330), lower := (rows 305 70 133 152 48 32 64 128 256), losses := [] }

theorem u5495 : Upper (D 1) (R 1) [304,68,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5495
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5496 : Route 9 := (fun mask => (mask,id))

def c5496 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5496 : Upper (D 1) (R 1) [304,68,129,144,64] 13 := by
  apply FastRouting.sound _ _ [304,68,129,144,64] 13 (by decide) (choices 1) [2,8] r5496 c5496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1951
  · exact u1952

def r5497 : Route 9 := (fun mask => (mask,id))

def c5497 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5497 : Upper (D 1) (R 1) [304,68,129,192,2] 13 := by
  apply FastRouting.sound _ _ [304,68,129,192,2] 13 (by decide) (choices 1) [2,8,16] r5497 c5497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1953
  · exact u1954
  · exact u1955

def b5498 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 70 133 200 24 50 114 178 306), lower := (rows 305 70 133 200 24 32 64 128 256), losses := [] }

theorem u5498 : Upper (D 1) (R 1) [304,68,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5498
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5499 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 133 200 48 58 90 154 282), lower := (rows 305 70 133 200 48 32 64 128 256), losses := [] }

theorem u5499 : Upper (D 1) (R 1) [304,68,129,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5499
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5500 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 134 73 18 184 248 184 440), lower := (rows 305 70 134 73 18 32 64 128 256), losses := [] }

theorem u5500 : Upper (D 1) (R 1) [304,68,130,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5500
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5501 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 305 70 134 73 24 178 242 178 434), lower := (rows 305 70 134 73 24 32 64 128 256), losses := [] }

theorem u5501 : Upper (D 1) (R 1) [304,68,130,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5501
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5502 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 134 73 48 186 218 154 410), lower := (rows 305 70 134 73 48 32 64 128 256), losses := [] }

theorem u5502 : Upper (D 1) (R 1) [304,68,130,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5502
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5503_2 : Upper (D 1) (R 1) [304,68,130,65,128,2] 13 :=
  permutation_upper _ _ _ [304,68,130,65,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1956

theorem m5503_8 : Upper (D 1) (R 1) [304,68,130,65,128,8] 13 :=
  permutation_upper _ _ _ [304,68,130,65,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1957

theorem m5503_16 : Upper (D 1) (R 1) [304,68,130,65,128,16] 13 :=
  permutation_upper _ _ _ [304,68,130,65,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1958

def r5503 : Route 9 := (fun mask => (mask,id))

def c5503 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5503 : Upper (D 1) (R 1) [304,68,130,65,128] 13 := by
  apply FastRouting.sound _ _ [304,68,130,65,128] 13 (by decide) (choices 1) [2,8,16] r5503 c5503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5503_2
  · exact m5503_8
  · exact m5503_16

def b5504 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 305 70 134 88 17 170 234 170 426), lower := (rows 305 70 134 88 17 32 64 128 256), losses := [] }

theorem u5504 : Upper (D 1) (R 1) [304,68,130,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5504
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5505 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 134 88 18 169 233 169 425), lower := (rows 305 70 134 88 18 32 64 128 256), losses := [] }

theorem u5505 : Upper (D 1) (R 1) [304,68,130,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5505
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5506 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 70 134 88 24 163 227 163 419), lower := (rows 305 70 134 88 24 32 64 128 256), losses := [] }

theorem u5506 : Upper (D 1) (R 1) [304,68,130,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5506
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5507 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 134 88 48 171 203 139 395), lower := (rows 305 70 134 88 48 32 64 128 256), losses := [] }

theorem u5507 : Upper (D 1) (R 1) [304,68,130,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5507
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5508 : PairBound 9 := { available := 43, camps := [], pairs := [(3,1)], upper := (rows 305 70 134 88 144 43 107 171 299), lower := (rows 305 70 134 88 144 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 148 32 64 128 256), good := (rows 305 92 156 88 144 32 64 144 256) }] }

theorem u5508 : Upper (D 1) (R 1) [304,68,130,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5508
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5509 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 134 137 18 120 120 248 376), lower := (rows 305 70 134 137 18 32 64 128 256), losses := [] }

theorem u5509 : Upper (D 1) (R 1) [304,68,130,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5509
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5510 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 305 70 134 137 24 114 114 242 370), lower := (rows 305 70 134 137 24 32 64 128 256), losses := [] }

theorem u5510 : Upper (D 1) (R 1) [304,68,130,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5510
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5511 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 134 137 48 122 90 218 346), lower := (rows 305 70 134 137 48 32 64 128 256), losses := [] }

theorem u5511 : Upper (D 1) (R 1) [304,68,130,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5511
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5512_2 : Upper (D 1) (R 1) [304,68,130,129,64,2] 13 :=
  permutation_upper _ _ _ [304,68,130,129,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1959

theorem m5512_8 : Upper (D 1) (R 1) [304,68,130,129,64,8] 13 :=
  permutation_upper _ _ _ [304,68,130,129,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1960

theorem m5512_16 : Upper (D 1) (R 1) [304,68,130,129,64,16] 13 :=
  permutation_upper _ _ _ [304,68,130,129,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1961

def r5512 : Route 9 := (fun mask => (mask,id))

def c5512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5512 : Upper (D 1) (R 1) [304,68,130,129,64] 13 := by
  apply FastRouting.sound _ _ [304,68,130,129,64] 13 (by decide) (choices 1) [2,8,16] r5512 c5512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5512_2
  · exact m5512_8
  · exact m5512_16

def b5513 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 305 70 134 152 17 106 106 234 362), lower := (rows 305 70 134 152 17 32 64 128 256), losses := [] }

theorem u5513 : Upper (D 1) (R 1) [304,68,130,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5513
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5514 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 134 152 18 105 105 233 361), lower := (rows 305 70 134 152 18 32 64 128 256), losses := [] }

theorem u5514 : Upper (D 1) (R 1) [304,68,130,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5514
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5515 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 305 70 134 152 24 99 99 227 355), lower := (rows 305 70 134 152 24 32 64 128 256), losses := [] }

theorem u5515 : Upper (D 1) (R 1) [304,68,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5515
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5516 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 134 152 48 107 75 203 331), lower := (rows 305 70 134 152 48 32 64 128 256), losses := [] }

theorem u5516 : Upper (D 1) (R 1) [304,68,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5516
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5517 : PairBound 9 := { available := 43, camps := [], pairs := [(3,1)], upper := (rows 305 70 134 152 80 43 107 171 299), lower := (rows 305 70 134 152 80 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 82 32 64 128 256), good := (rows 305 92 156 152 80 32 80 128 256) }] }

theorem u5517 : Upper (D 1) (R 1) [304,68,130,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5517
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5518 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 140 11 18 240 240 240 496), lower := (rows 305 70 140 11 18 32 64 128 256), losses := [] }

theorem u5518 : Upper (D 1) (R 1) [304,68,136,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5518
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5519 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 140 11 48 242 210 210 466), lower := (rows 305 70 140 11 48 32 64 128 256), losses := [] }

theorem u5519 : Upper (D 1) (R 1) [304,68,136,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5519
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5519
end Delivery.IrregularNine14.P01
