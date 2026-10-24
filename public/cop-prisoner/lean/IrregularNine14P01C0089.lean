import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0030
import IrregularNine14P01C0031

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5340 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 22 100 138 24 227 195 195 451), lower := (rows 305 22 100 138 24 32 64 128 256), losses := [] }

theorem u5340 : Upper (D 1) (R 1) [304,20,96,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5340
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5341 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 138 80 171 203 139 395), lower := (rows 305 22 100 138 80 32 64 128 256), losses := [] }

theorem u5341 : Upper (D 1) (R 1) [304,20,96,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5341
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5342 : Route 9 := (fun mask => (mask,id))

def c5342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5342 : Upper (D 1) (R 1) [304,20,96,130,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,130,128] 13 (by decide) (choices 1) [1,2,8,64] r5342 c5342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1843
  · exact u1844
  · exact u1845
  · exact u1846

def b5343 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 22 100 200 17 170 202 138 394), lower := (rows 305 22 100 200 17 32 64 128 256), losses := [] }

theorem u5343 : Upper (D 1) (R 1) [304,20,96,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5343
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5344 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 100 200 18 171 203 139 395), lower := (rows 305 22 100 200 18 32 64 128 256), losses := [] }

theorem u5344 : Upper (D 1) (R 1) [304,20,96,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5344
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5345 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 100 200 24 163 195 131 387), lower := (rows 305 22 100 200 24 32 64 128 256), losses := [] }

theorem u5345 : Upper (D 1) (R 1) [304,20,96,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5346 : Route 9 := (fun mask => (mask,id))

def c5346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5346 : Upper (D 1) (R 1) [304,20,96,192,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,192,128] 13 (by decide) (choices 1) [1,2,8] r5346 c5346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1847
  · exact u1848
  · exact u1849

def b5347 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 305 22 196 42 17 234 202 202 458), lower := (rows 305 22 196 42 17 32 64 128 256), losses := [] }

theorem u5347 : Upper (D 1) (R 1) [304,20,192,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5347
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5348 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 196 42 18 233 201 201 457), lower := (rows 305 22 196 42 18 32 64 128 256), losses := [] }

theorem u5348 : Upper (D 1) (R 1) [304,20,192,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5348
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5349 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 22 196 42 24 227 195 195 451), lower := (rows 305 22 196 42 24 32 64 128 256), losses := [] }

theorem u5349 : Upper (D 1) (R 1) [304,20,192,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5349
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5350 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 196 42 80 171 203 139 395), lower := (rows 305 22 196 42 80 32 64 128 256), losses := [] }

theorem u5350 : Upper (D 1) (R 1) [304,20,192,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5350
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5351 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 196 73 18 170 234 170 426), lower := (rows 305 22 196 73 18 32 64 128 256), losses := [] }

theorem u5351 : Upper (D 1) (R 1) [304,20,192,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5351
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5352 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 22 196 73 24 162 226 162 418), lower := (rows 305 22 196 73 24 32 64 128 256), losses := [] }

theorem u5352 : Upper (D 1) (R 1) [304,20,192,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5352
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5353 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 196 73 48 170 202 138 394), lower := (rows 305 22 196 73 48 32 64 128 256), losses := [] }

theorem u5353 : Upper (D 1) (R 1) [304,20,192,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5353
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5354 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 196 73 144 42 106 170 298), lower := (rows 305 22 196 73 144 32 64 128 256), losses := [] }

theorem u5354 : Upper (D 1) (R 1) [304,20,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5354
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5355 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 22 196 104 17 170 202 138 394), lower := (rows 305 22 196 104 17 32 64 128 256), losses := [] }

theorem u5355 : Upper (D 1) (R 1) [304,20,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5355
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5356 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 196 104 18 171 203 139 395), lower := (rows 305 22 196 104 18 32 64 128 256), losses := [] }

theorem u5356 : Upper (D 1) (R 1) [304,20,192,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5356
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5357 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 196 104 24 163 195 131 387), lower := (rows 305 22 196 104 24 32 64 128 256), losses := [] }

theorem u5357 : Upper (D 1) (R 1) [304,20,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5357
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5358 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 196 104 144 43 75 139 267), lower := (rows 305 22 196 104 144 32 64 128 256), losses := [] }

theorem u5358 : Upper (D 1) (R 1) [304,20,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5358
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5359 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 67 14 140 18 240 240 240 496), lower := (rows 305 67 14 140 18 32 64 128 256), losses := [] }

theorem u5359 : Upper (D 1) (R 1) [304,65,10,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5359
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5360 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 14 140 48 242 210 210 466), lower := (rows 305 67 14 140 48 32 64 128 256), losses := [] }

theorem u5360 : Upper (D 1) (R 1) [304,65,10,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5360
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5361_2 : Upper (D 1) (R 1) [304,65,10,132,64,2] 13 :=
  permutation_upper _ _ _ [304,65,10,132,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1850

theorem m5361_16 : Upper (D 1) (R 1) [304,65,10,132,64,16] 13 :=
  permutation_upper _ _ _ [304,65,10,132,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1851

def r5361 : Route 9 := (fun mask => (mask,id))

def c5361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5361 : Upper (D 1) (R 1) [304,65,10,132,64] 13 := by
  apply FastRouting.sound _ _ [304,65,10,132,64] 13 (by decide) (choices 1) [2,16,128] r5361 c5361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5361_2
  · exact m5361_16
  · exact u1852

def b5362 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 305 67 14 140 144 114 114 242 370), lower := (rows 305 67 14 140 144 32 64 128 256), losses := [] }

theorem u5362 : Upper (D 1) (R 1) [304,65,10,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5362
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5363 : Route 9 := (fun mask => (mask,id))

def c5363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5363 : Upper (D 1) (R 1) [304,65,10,144,2] 13 := by
  apply FastRouting.sound _ _ [304,65,10,144,2] 13 (by decide) (choices 1) [4,64,128] r5363 c5363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1853
  · exact u1854
  · exact u1855

def b5364 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 67 14 152 20 226 226 226 482), lower := (rows 305 67 14 152 20 32 64 128 256), losses := [] }

theorem u5364 : Upper (D 1) (R 1) [304,65,10,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5364
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5365 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 14 152 48 230 198 198 454), lower := (rows 305 67 14 152 48 32 64 128 256), losses := [] }

theorem u5365 : Upper (D 1) (R 1) [304,65,10,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5365
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5366 : Route 9 := (fun mask => (mask,id))

def c5366 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5366 : Upper (D 1) (R 1) [304,65,10,144,64] 13 := by
  apply FastRouting.sound _ _ [304,65,10,144,64] 13 (by decide) (choices 1) [2,4,128] r5366 c5366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1856
  · exact u1857
  · exact u1858

def b5367 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 67 14 152 144 102 102 230 358), lower := (rows 305 67 14 152 144 32 64 128 256), losses := [] }

theorem u5367 : Upper (D 1) (R 1) [304,65,10,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5367
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5368 : Route 9 := (fun mask => (mask,id))

def c5368 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5368 : Upper (D 1) (R 1) [304,65,24,96,2] 13 := by
  apply FastRouting.sound _ _ [304,65,24,96,2] 13 (by decide) (choices 1) [2,4,128] r5368 c5368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1859
  · exact u1860
  · exact u1861

def b5369 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 67 28 104 20 162 194 130 386), lower := (rows 305 67 28 104 20 32 64 128 256), losses := [] }

theorem u5369 : Upper (D 1) (R 1) [304,65,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5369
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5370 : Route 9 := (fun mask => (mask,id))

def c5370 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5370 : Upper (D 1) (R 1) [304,65,24,96,128] 13 := by
  apply FastRouting.sound _ _ [304,65,24,96,128] 13 (by decide) (choices 1) [2,4,128] r5370 c5370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1862
  · exact u1863
  · exact u1864

def b5371 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 28 138 18 228 228 228 484), lower := (rows 305 67 28 138 18 32 64 128 256), losses := [] }

theorem u5371 : Upper (D 1) (R 1) [304,65,24,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5371
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5372 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 67 28 138 20 226 226 226 482), lower := (rows 305 67 28 138 20 32 64 128 256), losses := [] }

theorem u5372 : Upper (D 1) (R 1) [304,65,24,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5372
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5373 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 28 138 48 230 198 198 454), lower := (rows 305 67 28 138 48 32 64 128 256), losses := [] }

theorem u5373 : Upper (D 1) (R 1) [304,65,24,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5373
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5374 : PairBound 9 := { available := 166, camps := [], pairs := [(2,1)], upper := (rows 305 67 28 138 80 166 230 166 422), lower := (rows 305 67 28 138 80 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 82 32 64 128 256), good := (rows 305 81 28 156 80 32 80 128 256) }] }

theorem u5374 : Upper (D 1) (R 1) [304,65,24,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5374
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5375 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 28 138 144 102 102 230 358), lower := (rows 305 67 28 138 144 32 64 128 256), losses := [] }

theorem u5375 : Upper (D 1) (R 1) [304,65,24,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5375
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5376 : Route 9 := (fun mask => (mask,id))

def c5376 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5376 : Upper (D 1) (R 1) [304,65,24,160,2] 13 := by
  apply FastRouting.sound _ _ [304,65,24,160,2] 13 (by decide) (choices 1) [2,4,64,128] r5376 c5376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1865
  · exact u1866
  · exact u1867
  · exact u1868

def b5377 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 305 67 28 168 20 226 194 194 450), lower := (rows 305 67 28 168 20 32 64 128 256), losses := [] }

theorem u5377 : Upper (D 1) (R 1) [304,65,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5377
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5378 : Route 9 := (fun mask => (mask,id))

def c5378 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5378 : Upper (D 1) (R 1) [304,65,24,160,64] 13 := by
  apply FastRouting.sound _ _ [304,65,24,160,64] 13 (by decide) (choices 1) [2,4,128] r5378 c5378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1869
  · exact u1870
  · exact u1871

def b5379 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 28 168 144 102 70 198 326), lower := (rows 305 67 28 168 144 32 64 128 256), losses := [] }

theorem u5379 : Upper (D 1) (R 1) [304,65,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5379
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5380 : Route 9 := (fun mask => (mask,id))

def c5380 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5380 : Upper (D 1) (R 1) [304,65,24,192,2] 13 := by
  apply FastRouting.sound _ _ [304,65,24,192,2] 13 (by decide) (choices 1) [2,4,128] r5380 c5380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1872
  · exact u1873
  · exact u1874

def b5381 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 67 28 200 20 162 226 162 418), lower := (rows 305 67 28 200 20 32 64 128 256), losses := [] }

theorem u5381 : Upper (D 1) (R 1) [304,65,24,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5381
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5382 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 28 200 48 166 198 134 390), lower := (rows 305 67 28 200 48 32 64 128 256), losses := [] }

theorem u5382 : Upper (D 1) (R 1) [304,65,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5382
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5383 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 28 200 144 38 102 166 294), lower := (rows 305 67 28 200 144 32 64 128 256), losses := [] }

theorem u5383 : Upper (D 1) (R 1) [304,65,24,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5383
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5384 : PairBound 9 := { available := 180, camps := [], pairs := [(0,6)], upper := (rows 305 67 76 138 18 180 244 180 436), lower := (rows 305 67 76 138 18 32 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 26 36 0 132 260), good := (rows 305 19 445 154 18 32 0 128 256) }] }

theorem u5384 : Upper (D 1) (R 1) [304,65,72,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5384
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5385 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 305 67 76 138 20 178 242 178 434), lower := (rows 305 67 76 138 20 32 64 128 256), losses := [] }

theorem u5385 : Upper (D 1) (R 1) [304,65,72,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5385
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5386 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 76 138 48 182 214 150 406), lower := (rows 305 67 76 138 48 32 64 128 256), losses := [] }

theorem u5386 : Upper (D 1) (R 1) [304,65,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5386
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5387_2 : Upper (D 1) (R 1) [304,65,72,130,128,2] 13 :=
  permutation_upper _ _ _ [304,65,72,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1875

theorem m5387_4 : Upper (D 1) (R 1) [304,65,72,130,128,4] 13 :=
  permutation_upper _ _ _ [304,65,72,130,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1876

theorem m5387_16 : Upper (D 1) (R 1) [304,65,72,130,128,16] 13 :=
  permutation_upper _ _ _ [304,65,72,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1877

def r5387 : Route 9 := (fun mask => (mask,id))

def c5387 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5387 : Upper (D 1) (R 1) [304,65,72,130,128] 13 := by
  apply FastRouting.sound _ _ [304,65,72,130,128] 13 (by decide) (choices 1) [2,4,16] r5387 c5387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5387_2
  · exact m5387_4
  · exact m5387_16

def r5388 : Route 9 := (fun mask => (mask,id))

def c5388 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5388 : Upper (D 1) (R 1) [304,65,72,144,2] 13 := by
  apply FastRouting.sound _ _ [304,65,72,144,2] 13 (by decide) (choices 1) [2,4,128] r5388 c5388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1878
  · exact u1879
  · exact u1880

def b5389 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 67 76 152 20 162 226 162 418), lower := (rows 305 67 76 152 20 32 64 128 256), losses := [] }

theorem u5389 : Upper (D 1) (R 1) [304,65,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5389
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5390 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 76 152 48 166 198 134 390), lower := (rows 305 67 76 152 48 32 64 128 256), losses := [] }

theorem u5390 : Upper (D 1) (R 1) [304,65,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5390
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5391 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 67 76 152 144 38 102 166 294), lower := (rows 305 67 76 152 144 32 64 128 256), losses := [] }

theorem u5391 : Upper (D 1) (R 1) [304,65,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5391
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5392 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 84 138 18 172 236 172 428), lower := (rows 305 67 84 138 18 32 64 128 256), losses := [] }

theorem u5392 : Upper (D 1) (R 1) [304,65,80,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5392
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5393 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 305 67 84 138 20 170 234 170 426), lower := (rows 305 67 84 138 20 32 64 128 256), losses := [] }

theorem u5393 : Upper (D 1) (R 1) [304,65,80,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5393
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5394 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 305 67 84 138 24 166 230 166 422), lower := (rows 305 67 84 138 24 32 64 128 256), losses := [] }

theorem u5394 : Upper (D 1) (R 1) [304,65,80,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5394
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5395 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 84 138 48 174 206 142 398), lower := (rows 305 67 84 138 48 32 64 128 256), losses := [] }

theorem u5395 : Upper (D 1) (R 1) [304,65,80,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5395
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5396 : Route 9 := (fun mask => (mask,id))

def c5396 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5396 : Upper (D 1) (R 1) [304,65,80,130,128] 13 := by
  apply FastRouting.sound _ _ [304,65,80,130,128] 13 (by decide) (choices 1) [2,4,8] r5396 c5396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1881
  · exact u1882
  · exact u1883

def b5397 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 84 140 18 170 234 170 426), lower := (rows 305 67 84 140 18 32 64 128 256), losses := [] }

theorem u5397 : Upper (D 1) (R 1) [304,65,80,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5397
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5398 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 67 84 140 24 162 226 162 418), lower := (rows 305 67 84 140 24 32 64 128 256), losses := [] }

theorem u5398 : Upper (D 1) (R 1) [304,65,80,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5398
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5399 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 84 140 48 170 202 138 394), lower := (rows 305 67 84 140 48 32 64 128 256), losses := [] }

theorem u5399 : Upper (D 1) (R 1) [304,65,80,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5399
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5399
end Delivery.IrregularNine14.P01
