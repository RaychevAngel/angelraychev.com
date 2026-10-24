import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0029
import IrregularNine14P06C0030

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11340 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 56, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 162 324 25 56 33 70 198 326), lower := (rows 7 162 324 25 56 33 64 128 256), losses := [] }

theorem u11340 : Upper (D 6) (R 6) [6,160,320,17,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11340
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11341 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 162 324 25 56 34 69 197 325), lower := (rows 7 162 324 25 56 34 64 128 256), losses := [] }

theorem u11341 : Upper (D 6) (R 6) [6,160,320,17,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11341
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11342 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 162 324 25 56 36 67 195 323), lower := (rows 7 162 324 25 56 36 64 128 256), losses := [] }

theorem u11342 : Upper (D 6) (R 6) [6,160,320,17,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11342
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11343 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5),(3,1)], upper := (rows 7 162 324 25 56 96 71 135 263), lower := (rows 7 162 324 25 56 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 100 64 128 256), good := (rows 61 160 356 25 56 96 96 128 256) }] }

theorem u11343 : Upper (D 6) (R 6) [6,160,320,17,40,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11343
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11344 : Route 9 := (fun mask => (mask,id))

def c11344 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11344 : Upper (D 6) (R 6) [6,160,320,17,96,1] 13 := by
  apply FastRouting.sound _ _ [6,160,320,17,96,1] 13 (by decide) (choices 1) [2,4,8] r11344 c11344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1784
  · exact u1785
  · exact u1786

def b11345 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 162 324 25 112 34 77 141 269), lower := (rows 7 162 324 25 112 34 64 128 256), losses := [] }

theorem u11345 : Upper (D 6) (R 6) [6,160,320,17,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11345
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11346 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 7 162 324 25 112 36 75 139 267), lower := (rows 7 162 324 25 112 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 20 37 64 128 256), good := (rows 61 160 372 57 112 52 64 128 256) }] }

theorem u11346 : Upper (D 6) (R 6) [6,160,320,17,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11346
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11347 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 162 324 25 112 40 71 135 263), lower := (rows 7 162 324 25 112 40 64 128 256), losses := [] }

theorem u11347 : Upper (D 6) (R 6) [6,160,320,17,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11347
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11348 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 162 324 26 49 33 76 204 332), lower := (rows 7 162 324 26 49 33 64 128 256), losses := [] }

theorem u11348 : Upper (D 6) (R 6) [6,160,320,18,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11348
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11349 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 56, targets := 64 },{ cop := 3, region := 325, targets := 32 }], pairs := [(0,5),(3,6),(4,6)], upper := (rows 7 162 324 26 49 36 73 201 329), lower := (rows 7 162 324 26 49 36 64 128 256), losses := [] }

theorem u11349 : Upper (D 6) (R 6) [6,160,320,18,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11349
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11350 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 7 162 324 26 49 40 69 197 325), lower := (rows 7 162 324 26 49 40 64 128 256), losses := [] }

theorem u11350 : Upper (D 6) (R 6) [6,160,320,18,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11350
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11351 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 325, targets := 32 }], pairs := [(0,5),(2,5),(4,1)], upper := (rows 7 162 324 26 49 96 77 141 269), lower := (rows 7 162 324 26 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 100 64 128 256), good := (rows 53 160 356 24 49 96 96 128 256) }] }

theorem u11351 : Upper (D 6) (R 6) [6,160,320,18,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11351
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11352 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 56, targets := 64 },{ cop := 3, region := 325, targets := 32 }], pairs := [(0,5),(3,6),(4,6)], upper := (rows 7 162 324 26 52 33 73 201 329), lower := (rows 7 162 324 26 52 33 64 128 256), losses := [] }

theorem u11352 : Upper (D 6) (R 6) [6,160,320,18,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11352
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11353 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 162 324 26 52 40 65 193 321), lower := (rows 7 162 324 26 52 40 64 128 256), losses := [] }

theorem u11353 : Upper (D 6) (R 6) [6,160,320,18,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11353
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11354 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 162 324 26 52 96 73 137 265), lower := (rows 7 162 324 26 52 96 64 128 256), losses := [] }

theorem u11354 : Upper (D 6) (R 6) [6,160,320,18,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11354
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11355 : Route 9 := (fun mask => (mask,id))

def c11355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11355 : Upper (D 6) (R 6) [6,160,320,18,65,1] 13 := by
  apply FastRouting.sound _ _ [6,160,320,18,65,1] 13 (by decide) (choices 1) [4,8,32] r11355 c11355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1787
  · exact u1788
  · exact u1789

def r11356 : Route 9 := (fun mask => (mask,id))

def c11356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11356 : Upper (D 6) (R 6) [6,160,320,18,65,4] 13 := by
  apply FastRouting.sound _ _ [6,160,320,18,65,4] 13 (by decide) (choices 1) [1,8,32] r11356 c11356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1790
  · exact u1791
  · exact u1792

def r11357 : Route 9 := (fun mask => (mask,id))

def c11357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11357 : Upper (D 6) (R 6) [6,160,320,18,65,8] 13 := by
  apply FastRouting.sound _ _ [6,160,320,18,65,8] 13 (by decide) (choices 1) [1,4,32] r11357 c11357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1793
  · exact u1794
  · exact u1795

def r11358 : Route 9 := (fun mask => (mask,id))

def c11358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11358 : Upper (D 6) (R 6) [6,160,320,18,96,1] 13 := by
  apply FastRouting.sound _ _ [6,160,320,18,96,1] 13 (by decide) (choices 1) [1,4,8] r11358 c11358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1796
  · exact u1797
  · exact u1798

def b11359 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 325, targets := 32 }], pairs := [(0,5),(4,0),(4,1)], upper := (rows 7 162 324 26 112 36 73 137 265), lower := (rows 7 162 324 26 112 36 64 128 256), losses := [] }

theorem u11359 : Upper (D 6) (R 6) [6,160,320,18,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11359
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11360 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 162 324 26 112 40 69 133 261), lower := (rows 7 162 324 26 112 40 64 128 256), losses := [] }

theorem u11360 : Upper (D 6) (R 6) [6,160,320,18,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11360
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11361 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 162 324 41 81 34 92 156 284), lower := (rows 7 162 324 41 81 34 64 128 256), losses := [] }

theorem u11361 : Upper (D 6) (R 6) [6,160,320,33,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11361
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11362 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 210, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 162 324 41 81 36 90 154 282), lower := (rows 7 162 324 41 81 36 64 128 256), losses := [] }

theorem u11362 : Upper (D 6) (R 6) [6,160,320,33,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11362
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11363 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 162 324 41 81 40 86 150 278), lower := (rows 7 162 324 41 81 40 64 128 256), losses := [] }

theorem u11363 : Upper (D 6) (R 6) [6,160,320,33,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11363
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11364 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 162 324 41 81 48 78 142 270), lower := (rows 7 162 324 41 81 48 64 128 256), losses := [] }

theorem u11364 : Upper (D 6) (R 6) [6,160,320,33,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11364
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11365 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 162 324 41 82 33 92 156 284), lower := (rows 7 162 324 41 82 33 64 128 256), losses := [] }

theorem u11365 : Upper (D 6) (R 6) [6,160,320,33,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11365
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11366 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 210, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 162 324 41 82 36 89 153 281), lower := (rows 7 162 324 41 82 36 64 128 256), losses := [] }

theorem u11366 : Upper (D 6) (R 6) [6,160,320,33,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11366
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11367 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 162 324 41 82 40 85 149 277), lower := (rows 7 162 324 41 82 40 64 128 256), losses := [] }

theorem u11367 : Upper (D 6) (R 6) [6,160,320,33,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11367
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11368 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 162 324 41 82 48 77 141 269), lower := (rows 7 162 324 41 82 48 64 128 256), losses := [] }

theorem u11368 : Upper (D 6) (R 6) [6,160,320,33,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11368
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11369 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 162 324 41 88 33 86 150 278), lower := (rows 7 162 324 41 88 33 64 128 256), losses := [] }

theorem u11369 : Upper (D 6) (R 6) [6,160,320,33,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11369
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11370 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 162 324 41 88 34 85 149 277), lower := (rows 7 162 324 41 88 34 64 128 256), losses := [] }

theorem u11370 : Upper (D 6) (R 6) [6,160,320,33,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11370
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11371 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 3, region := 210, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 162 324 41 88 36 83 147 275), lower := (rows 7 162 324 41 88 36 64 128 256), losses := [] }

theorem u11371 : Upper (D 6) (R 6) [6,160,320,33,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11371
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11372 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 162 324 41 88 48 71 135 263), lower := (rows 7 162 324 41 88 48 64 128 256), losses := [] }

theorem u11372 : Upper (D 6) (R 6) [6,160,320,33,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11372
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11373 : Route 9 := (fun mask => (mask,id))

def c11373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11373 : Upper (D 6) (R 6) [6,160,320,36,66,1] 13 := by
  apply FastRouting.sound _ _ [6,160,320,36,66,1] 13 (by decide) (choices 1) [1,8,16] r11373 c11373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1799
  · exact u1800
  · exact u1801

def b11374 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 341, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 162 324 44 82 40 81 145 273), lower := (rows 7 162 324 44 82 40 64 128 256), losses := [] }

theorem u11374 : Upper (D 6) (R 6) [6,160,320,36,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11374
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11375 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 162 324 44 82 48 73 137 265), lower := (rows 7 162 324 44 82 48 64 128 256), losses := [] }

theorem u11375 : Upper (D 6) (R 6) [6,160,320,36,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11375
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11376 : Route 9 := (fun mask => (mask,id))

def c11376 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11376 : Upper (D 6) (R 6) [6,160,320,36,72,1] 13 := by
  apply FastRouting.sound _ _ [6,160,320,36,72,1] 13 (by decide) (choices 1) [1,2,16] r11376 c11376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1802
  · exact u1803
  · exact u1804

def b11377 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 162 324 44 88 34 81 145 273), lower := (rows 7 162 324 44 88 34 64 128 256), losses := [] }

theorem u11377 : Upper (D 6) (R 6) [6,160,320,36,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11377
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11378 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 162 324 44 88 48 67 131 259), lower := (rows 7 162 324 44 88 48 64 128 256), losses := [] }

theorem u11378 : Upper (D 6) (R 6) [6,160,320,36,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11378
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11379 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 76 112 34 452 388 388), lower := (rows 11 19 37 76 112 34 64 128 256), losses := [] }

theorem u11379 : Upper (D 6) (R 6) [10,17,33,68,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11379
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11380 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 466, targets := 4 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,2),(4,0),(4,2)], upper := (rows 11 19 37 76 112 36 450 386 386), lower := (rows 11 19 37 76 112 36 64 128 256), losses := [] }

theorem u11380 : Upper (D 6) (R 6) [10,17,33,68,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11380
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11381 : Route 9 := (fun mask => (mask,id))

def c11381 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u11381 : Upper (D 6) (R 6) [10,17,33,68,96,128] 13 := by
  apply FastRouting.sound _ _ [10,17,33,68,96,128] 13 (by decide) (choices 1) [2,4,256] r11381 c11381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1805
  · exact u1806
  · exact u1807

def b11382 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 76 148 34 352 480 352), lower := (rows 11 19 37 76 148 34 64 128 256), losses := [] }

theorem u11382 : Upper (D 6) (R 6) [10,17,33,68,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11382
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11383 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 19 37 76 148 96 354 418 290), lower := (rows 11 19 37 76 148 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 111 67 131 259), good := (rows 490 498 508 124 188 96 96 128 256) }] }

theorem u11383 : Upper (D 6) (R 6) [10,17,33,68,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11383
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11384 : PairBound 9 := { available := 98, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 19 37 76 148 288 98 226 354), lower := (rows 11 19 37 76 148 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 295 67 131 259), good := (rows 490 498 508 124 188 288 64 128 288) }] }

theorem u11384 : Upper (D 6) (R 6) [10,17,33,68,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11384
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11385 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 76 176 34 324 452 324), lower := (rows 11 19 37 76 176 34 64 128 256), losses := [] }

theorem u11385 : Upper (D 6) (R 6) [10,17,33,68,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11385
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11386 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 19 37 76 176 36 322 450 322), lower := (rows 11 19 37 76 176 36 64 128 256), losses := [] }

theorem u11386 : Upper (D 6) (R 6) [10,17,33,68,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11386
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11387 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 19 37 76 176 96 326 390 262), lower := (rows 11 19 37 76 176 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 21 37 108 176 96 96 128 256) }] }

theorem u11387 : Upper (D 6) (R 6) [10,17,33,68,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11387
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11388 : Route 9 := (fun mask => (mask,id))

def c11388 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11388 : Upper (D 6) (R 6) [10,17,33,68,160,256] 13 := by
  apply FastRouting.sound _ _ [10,17,33,68,160,256] 13 (by decide) (choices 1) [2,4] r11388 c11388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1808
  · exact u1809

def b11389 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 76 208 34 356 420 292), lower := (rows 11 19 37 76 208 34 64 128 256), losses := [] }

theorem u11389 : Upper (D 6) (R 6) [10,17,33,68,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11389
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11390 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 466, targets := 4 },{ cop := 0, region := 36, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 11 19 37 76 208 36 354 418 290), lower := (rows 11 19 37 76 208 36 64 128 256), losses := [] }

theorem u11390 : Upper (D 6) (R 6) [10,17,33,68,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11390
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11391 : Route 9 := (fun mask => (mask,id))

def c11391 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11391 : Upper (D 6) (R 6) [10,17,33,68,192,256] 13 := by
  apply FastRouting.sound _ _ [10,17,33,68,192,256] 13 (by decide) (choices 1) [2,4,32] r11391 c11391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1810
  · exact u1811
  · exact u1812

def b11392 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 76 400 34 100 228 356), lower := (rows 11 19 37 76 400 34 64 128 256), losses := [] }

theorem u11392 : Upper (D 6) (R 6) [10,17,33,68,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11392
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11393 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 19 37 76 400 36 98 226 354), lower := (rows 11 19 37 76 400 36 64 128 256), losses := [] }

theorem u11393 : Upper (D 6) (R 6) [10,17,33,68,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11393
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11394 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 19 37 76 400 96 102 166 294), lower := (rows 11 19 37 76 400 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 21 37 108 400 96 96 128 256) }] }

theorem u11394 : Upper (D 6) (R 6) [10,17,33,68,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11394
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11395 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 104 148 34 324 452 324), lower := (rows 11 19 37 104 148 34 64 128 256), losses := [] }

theorem u11395 : Upper (D 6) (R 6) [10,17,33,96,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11395
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11396 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 19 37 104 148 36 322 450 322), lower := (rows 11 19 37 104 148 36 64 128 256), losses := [] }

theorem u11396 : Upper (D 6) (R 6) [10,17,33,96,132,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11396
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11397 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 37 104 148 96 326 390 262), lower := (rows 11 19 37 104 148 96 64 128 256), losses := [] }

theorem u11397 : Upper (D 6) (R 6) [10,17,33,96,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11397
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11398 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 19 37 104 148 288 70 198 326), lower := (rows 11 19 37 104 148 288 64 128 256), losses := [] }

theorem u11398 : Upper (D 6) (R 6) [10,17,33,96,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11398
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11399 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 104 400 34 68 196 324), lower := (rows 11 19 37 104 400 34 64 128 256), losses := [] }

theorem u11399 : Upper (D 6) (R 6) [10,17,33,96,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11399
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11399
end Delivery.IrregularNine14.P06
