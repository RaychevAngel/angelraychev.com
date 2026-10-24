import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0030

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11400 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 19 37 104 400 36 70 198 326), lower := (rows 11 19 37 104 400 36 64 128 256), losses := [] }

theorem u11400 : Upper (D 6) (R 6) [10,17,33,96,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11400
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11401 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 37 104 400 96 70 134 262), lower := (rows 11 19 37 104 400 96 64 128 256), losses := [] }

theorem u11401 : Upper (D 6) (R 6) [10,17,33,96,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11401
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11402 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 140 84 34 352 480 352), lower := (rows 11 19 37 140 84 34 64 128 256), losses := [] }

theorem u11402 : Upper (D 6) (R 6) [10,17,33,132,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11402
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11403 : PairBound 9 := { available := 290, camps := [], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 19 37 140 84 96 354 418 290), lower := (rows 11 19 37 140 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 119 67 131 259), good := (rows 490 498 508 188 124 96 96 128 256) },{ target := 1, region := (rows 1 0 6 8 16 112 64 128 256), good := (rows 13 53 37 140 116 96 96 128 256) }] }

theorem u11403 : Upper (D 6) (R 6) [10,17,33,132,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11403
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11404 : PairBound 9 := { available := 98, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 19 37 140 84 288 98 226 354), lower := (rows 11 19 37 140 84 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 295 67 131 259), good := (rows 490 498 508 188 124 288 64 128 288) }] }

theorem u11404 : Upper (D 6) (R 6) [10,17,33,132,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11404
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11405 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 140 112 34 324 452 324), lower := (rows 11 19 37 140 112 34 64 128 256), losses := [] }

theorem u11405 : Upper (D 6) (R 6) [10,17,33,132,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11405
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11406 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 19 37 140 112 36 322 450 322), lower := (rows 11 19 37 140 112 36 64 128 256), losses := [] }

theorem u11406 : Upper (D 6) (R 6) [10,17,33,132,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11406
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11407 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 37 140 112 96 326 390 262), lower := (rows 11 19 37 140 112 96 64 128 256), losses := [] }

theorem u11407 : Upper (D 6) (R 6) [10,17,33,132,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11407
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11408 : Route 9 := (fun mask => (mask,id))

def c11408 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11408 : Upper (D 6) (R 6) [10,17,33,132,96,256] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132,96,256] 13 (by decide) (choices 1) [2,4] r11408 c11408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1813
  · exact u1814

def b11409 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 140 276 34 96 224 352), lower := (rows 11 19 37 140 276 34 64 128 256), losses := [] }

theorem u11409 : Upper (D 6) (R 6) [10,17,33,132,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11409
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11410 : Route 9 := (fun mask => (mask,id))

def c11410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11410 : Upper (D 6) (R 6) [10,17,33,132,260,64] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132,260,64] 13 (by decide) (choices 1) [2,32] r11410 c11410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1815
  · exact u1816

def b11411 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 140 304 34 68 196 324), lower := (rows 11 19 37 140 304 34 64 128 256), losses := [] }

theorem u11411 : Upper (D 6) (R 6) [10,17,33,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11411
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11412 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 19 37 140 304 36 66 194 322), lower := (rows 11 19 37 140 304 36 64 128 256), losses := [] }

theorem u11412 : Upper (D 6) (R 6) [10,17,33,132,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11412
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11413 : Route 9 := (fun mask => (mask,id))

def c11413 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11413 : Upper (D 6) (R 6) [10,17,33,132,288,64] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132,288,64] 13 (by decide) (choices 1) [2,4] r11413 c11413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1817
  · exact u1818

def b11414 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 140 336 34 100 228 356), lower := (rows 11 19 37 140 336 34 64 128 256), losses := [] }

theorem u11414 : Upper (D 6) (R 6) [10,17,33,132,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11414
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11415 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 19 37 140 336 36 98 226 354), lower := (rows 11 19 37 140 336 36 64 128 256), losses := [] }

theorem u11415 : Upper (D 6) (R 6) [10,17,33,132,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11415
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11416 : Route 9 := (fun mask => (mask,id))

def c11416 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11416 : Upper (D 6) (R 6) [10,17,33,132,320,64] 13 := by
  apply FastRouting.sound _ _ [10,17,33,132,320,64] 13 (by decide) (choices 1) [2,4,32] r11416 c11416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1819
  · exact u1820
  · exact u1821

def b11417 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 168 84 34 324 452 324), lower := (rows 11 19 37 168 84 34 64 128 256), losses := [] }

theorem u11417 : Upper (D 6) (R 6) [10,17,33,160,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11417
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11418 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 19 37 168 84 36 322 450 322), lower := (rows 11 19 37 168 84 36 64 128 256), losses := [] }

theorem u11418 : Upper (D 6) (R 6) [10,17,33,160,68,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11418
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11419 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 19 37 168 84 96 326 390 262), lower := (rows 11 19 37 168 84 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 8 16 112 64 128 256), good := (rows 13 53 37 168 116 96 96 128 256) }] }

theorem u11419 : Upper (D 6) (R 6) [10,17,33,160,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11419
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11420 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 82, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 19 37 168 84 288 70 198 326), lower := (rows 11 19 37 168 84 288 64 128 256), losses := [] }

theorem u11420 : Upper (D 6) (R 6) [10,17,33,160,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11420
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11421 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 168 276 34 68 196 324), lower := (rows 11 19 37 168 276 34 64 128 256), losses := [] }

theorem u11421 : Upper (D 6) (R 6) [10,17,33,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11421
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11422 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 19 37 168 276 36 66 194 322), lower := (rows 11 19 37 168 276 36 64 128 256), losses := [] }

theorem u11422 : Upper (D 6) (R 6) [10,17,33,160,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11422
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11423 : Route 9 := (fun mask => (mask,id))

def c11423 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11423 : Upper (D 6) (R 6) [10,17,33,160,260,64] 13 := by
  apply FastRouting.sound _ _ [10,17,33,160,260,64] 13 (by decide) (choices 1) [2,4] r11423 c11423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1822
  · exact u1823

def b11424 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 168 336 34 68 196 324), lower := (rows 11 19 37 168 336 34 64 128 256), losses := [] }

theorem u11424 : Upper (D 6) (R 6) [10,17,33,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11424
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11425 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 19 37 168 336 36 70 198 326), lower := (rows 11 19 37 168 336 36 64 128 256), losses := [] }

theorem u11425 : Upper (D 6) (R 6) [10,17,33,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11425
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11426 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 19 37 168 336 96 70 134 262), lower := (rows 11 19 37 168 336 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 8 16 112 64 128 256), good := (rows 13 53 37 168 368 96 96 128 256) }] }

theorem u11426 : Upper (D 6) (R 6) [10,17,33,160,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11426
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11427 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 200 84 34 356 420 292), lower := (rows 11 19 37 200 84 34 64 128 256), losses := [] }

theorem u11427 : Upper (D 6) (R 6) [10,17,33,192,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11427
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11428 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 19 37 200 84 36 354 418 290), lower := (rows 11 19 37 200 84 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 11 16 52 66 130 258), good := (rows 458 506 44 200 116 36 64 128 256) }] }

theorem u11428 : Upper (D 6) (R 6) [10,17,33,192,68,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11428
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11429 : Route 9 := (fun mask => (mask,id))

def c11429 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11429 : Upper (D 6) (R 6) [10,17,33,192,68,256] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,68,256] 13 (by decide) (choices 1) [2,4,32] r11429 c11429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1824
  · exact u1825
  · exact u1826

def b11430 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 200 112 34 324 388 260), lower := (rows 11 19 37 200 112 34 64 128 256), losses := [] }

theorem u11430 : Upper (D 6) (R 6) [10,17,33,192,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11430
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11431 : Route 9 := (fun mask => (mask,id))

def c11431 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u11431 : Upper (D 6) (R 6) [10,17,33,192,96,4] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,96,4] 13 (by decide) (choices 1) [2,4,256] r11431 c11431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1827
  · exact u1828
  · exact u1829

def r11432 : Route 9 := (fun mask => (mask,id))

def c11432 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11432 : Upper (D 6) (R 6) [10,17,33,192,96,256] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,96,256] 13 (by decide) (choices 1) [2,4] r11432 c11432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1830
  · exact u1831

def b11433 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 200 276 34 100 228 356), lower := (rows 11 19 37 200 276 34 64 128 256), losses := [] }

theorem u11433 : Upper (D 6) (R 6) [10,17,33,192,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11433
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11434 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 19 37 200 276 36 98 226 354), lower := (rows 11 19 37 200 276 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 11 16 52 66 130 258), good := (rows 458 506 44 200 308 36 64 128 256) }] }

theorem u11434 : Upper (D 6) (R 6) [10,17,33,192,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11434
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11435 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 274, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 19 37 200 276 96 102 166 294), lower := (rows 11 19 37 200 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 21 37 232 276 96 96 128 256) }] }

theorem u11435 : Upper (D 6) (R 6) [10,17,33,192,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11435
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11436 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 200 304 34 68 196 324), lower := (rows 11 19 37 200 304 34 64 128 256), losses := [] }

theorem u11436 : Upper (D 6) (R 6) [10,17,33,192,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11436
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11437 : Route 9 := (fun mask => (mask,id))

def c11437 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11437 : Upper (D 6) (R 6) [10,17,33,192,288,4] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,288,4] 13 (by decide) (choices 1) [2,4] r11437 c11437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1832
  · exact u1833

def b11438 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 274, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 19 37 200 304 96 70 134 262), lower := (rows 11 19 37 200 304 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 21 37 232 304 96 96 128 256) }] }

theorem u11438 : Upper (D 6) (R 6) [10,17,33,192,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11438
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11439 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 200 336 34 100 164 292), lower := (rows 11 19 37 200 336 34 64 128 256), losses := [] }

theorem u11439 : Upper (D 6) (R 6) [10,17,33,192,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11439
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11440 : Route 9 := (fun mask => (mask,id))

def c11440 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11440 : Upper (D 6) (R 6) [10,17,33,192,320,4] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,320,4] 13 (by decide) (choices 1) [2,4,32] r11440 c11440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1834
  · exact u1835
  · exact u1836

def b11441 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 392 84 34 100 228 356), lower := (rows 11 19 37 392 84 34 64 128 256), losses := [] }

theorem u11441 : Upper (D 6) (R 6) [10,17,33,384,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11441
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11442 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 19 37 392 84 36 98 226 354), lower := (rows 11 19 37 392 84 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 11 16 52 66 130 258), good := (rows 458 506 44 392 116 36 64 128 256) }] }

theorem u11442 : Upper (D 6) (R 6) [10,17,33,384,68,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11442
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11443 : Route 9 := (fun mask => (mask,id))

def c11443 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11443 : Upper (D 6) (R 6) [10,17,33,384,68,64] 13 := by
  apply FastRouting.sound _ _ [10,17,33,384,68,64] 13 (by decide) (choices 1) [2,4,32] r11443 c11443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1837
  · exact u1838
  · exact u1839

def b11444 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 392 112 34 68 196 324), lower := (rows 11 19 37 392 112 34 64 128 256), losses := [] }

theorem u11444 : Upper (D 6) (R 6) [10,17,33,384,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11444
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11445 : Route 9 := (fun mask => (mask,id))

def c11445 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11445 : Upper (D 6) (R 6) [10,17,33,384,96,4] 13 := by
  apply FastRouting.sound _ _ [10,17,33,384,96,4] 13 (by decide) (choices 1) [2,4] r11445 c11445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1840
  · exact u1841

def b11446 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 37 392 112 96 70 134 262), lower := (rows 11 19 37 392 112 96 64 128 256), losses := [] }

theorem u11446 : Upper (D 6) (R 6) [10,17,33,384,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11446
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11447 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 13 176 34 324 452 324), lower := (rows 11 19 100 13 176 34 64 128 256), losses := [] }

theorem u11447 : Upper (D 6) (R 6) [10,17,96,5,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11447
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11448 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 13 176 36 322 450 322), lower := (rows 11 19 100 13 176 36 64 128 256), losses := [] }

theorem u11448 : Upper (D 6) (R 6) [10,17,96,5,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11448
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11449 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 13 176 96 326 390 262), lower := (rows 11 19 100 13 176 96 64 128 256), losses := [] }

theorem u11449 : Upper (D 6) (R 6) [10,17,96,5,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11449
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11450 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 19 100 13 176 288 70 198 326), lower := (rows 11 19 100 13 176 288 64 128 256), losses := [] }

theorem u11450 : Upper (D 6) (R 6) [10,17,96,5,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11450
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11451 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 13 400 34 100 228 356), lower := (rows 11 19 100 13 400 34 64 128 256), losses := [] }

theorem u11451 : Upper (D 6) (R 6) [10,17,96,5,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11451
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11452 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 13 400 36 98 226 354), lower := (rows 11 19 100 13 400 36 64 128 256), losses := [] }

theorem u11452 : Upper (D 6) (R 6) [10,17,96,5,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11452
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11453 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 13 400 96 102 166 294), lower := (rows 11 19 100 13 400 96 64 128 256), losses := [] }

theorem u11453 : Upper (D 6) (R 6) [10,17,96,5,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11453
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11454 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 100 41 148 34 324 452 324), lower := (rows 11 19 100 41 148 34 64 128 256), losses := [] }

theorem u11454 : Upper (D 6) (R 6) [10,17,96,33,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11454
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11455 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 41 148 36 322 450 322), lower := (rows 11 19 100 41 148 36 64 128 256), losses := [] }

theorem u11455 : Upper (D 6) (R 6) [10,17,96,33,132,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11455
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11456 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 100 41 148 96 326 390 262), lower := (rows 11 19 100 41 148 96 64 128 256), losses := [] }

theorem u11456 : Upper (D 6) (R 6) [10,17,96,33,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11456
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11457 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 19 100 41 148 288 70 198 326), lower := (rows 11 19 100 41 148 288 64 128 256), losses := [] }

theorem u11457 : Upper (D 6) (R 6) [10,17,96,33,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11457
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11458 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 100 41 208 34 324 388 260), lower := (rows 11 19 100 41 208 34 64 128 256), losses := [] }

theorem u11458 : Upper (D 6) (R 6) [10,17,96,33,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11458
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11459 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 100 41 208 36 326 390 262), lower := (rows 11 19 100 41 208 36 64 128 256), losses := [] }

theorem u11459 : Upper (D 6) (R 6) [10,17,96,33,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11459
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11459
end Delivery.IrregularNine14.P06
