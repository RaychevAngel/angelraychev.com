import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0031
import IrregularNine14P01C0032

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5400 : Route 9 := (fun mask => (mask,id))

def c5400 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5400 : Upper (D 1) (R 1) [304,65,80,132,128] 13 := by
  apply FastRouting.sound _ _ [304,65,80,132,128] 13 (by decide) (choices 1) [2,8] r5400 c5400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1884
  · exact u1885

def b5401 : PairBound 9 := { available := 142, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 84 168 18 174 206 142 398), lower := (rows 305 67 84 168 18 32 64 128 256), losses := [] }

theorem u5401 : Upper (D 1) (R 1) [304,65,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5401
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5402 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 67 84 168 20 170 202 138 394), lower := (rows 305 67 84 168 20 32 64 128 256), losses := [] }

theorem u5402 : Upper (D 1) (R 1) [304,65,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5402
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5403 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 305 67 84 168 24 166 198 134 390), lower := (rows 305 67 84 168 24 32 64 128 256), losses := [] }

theorem u5403 : Upper (D 1) (R 1) [304,65,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5403
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5404 : Route 9 := (fun mask => (mask,id))

def c5404 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5404 : Upper (D 1) (R 1) [304,65,80,160,128] 13 := by
  apply FastRouting.sound _ _ [304,65,80,160,128] 13 (by decide) (choices 1) [2,4,8] r5404 c5404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1886
  · exact u1887
  · exact u1888

def b5405 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 67 134 152 18 108 108 236 364), lower := (rows 305 67 134 152 18 32 64 128 256), losses := [] }

theorem u5405 : Upper (D 1) (R 1) [304,65,130,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5405
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5406 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 305 67 134 152 20 106 106 234 362), lower := (rows 305 67 134 152 20 32 64 128 256), losses := [] }

theorem u5406 : Upper (D 1) (R 1) [304,65,130,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5406
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5407 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 305 67 134 152 24 102 102 230 358), lower := (rows 305 67 134 152 24 32 64 128 256), losses := [] }

theorem u5407 : Upper (D 1) (R 1) [304,65,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5407
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5408 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 134 152 48 110 78 206 334), lower := (rows 305 67 134 152 48 32 64 128 256), losses := [] }

theorem u5408 : Upper (D 1) (R 1) [304,65,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5408
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5409 : PairBound 9 := { available := 46, camps := [], pairs := [(3,1)], upper := (rows 305 67 134 152 80 46 110 174 302), lower := (rows 305 67 134 152 80 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 82 32 64 128 256), good := (rows 305 81 156 152 80 32 80 128 256) }] }

theorem u5409 : Upper (D 1) (R 1) [304,65,130,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5409
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5410 : Route 9 := (fun mask => (mask,id))

def c5410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5410 : Upper (D 1) (R 1) [304,65,130,192,2] 13 := by
  apply FastRouting.sound _ _ [304,65,130,192,2] 13 (by decide) (choices 1) [4,8,16] r5410 c5410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1889
  · exact u1890
  · exact u1891

def b5411 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 305 67 134 200 20 58 122 186 314), lower := (rows 305 67 134 200 20 32 64 128 256), losses := [] }

theorem u5411 : Upper (D 1) (R 1) [304,65,130,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5411
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5412 : PairBound 9 := { available := 54, camps := [], pairs := [], upper := (rows 305 67 134 200 24 54 118 182 310), lower := (rows 305 67 134 200 24 32 64 128 256), losses := [] }

theorem u5412 : Upper (D 1) (R 1) [304,65,130,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5412
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5413 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 134 200 48 62 94 158 286), lower := (rows 305 67 134 200 48 32 64 128 256), losses := [] }

theorem u5413 : Upper (D 1) (R 1) [304,65,130,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5413
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5414 : Route 9 := (fun mask => (mask,id))

def c5414 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5414 : Upper (D 1) (R 1) [304,65,144,160,2] 13 := by
  apply FastRouting.sound _ _ [304,65,144,160,2] 13 (by decide) (choices 1) [2,4,8,64] r5414 c5414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1892
  · exact u1893
  · exact u1894
  · exact u1895

def b5415 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 67 148 168 20 106 74 202 330), lower := (rows 305 67 148 168 20 32 64 128 256), losses := [] }

theorem u5415 : Upper (D 1) (R 1) [304,65,144,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5415
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5416 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 305 67 148 168 24 102 70 198 326), lower := (rows 305 67 148 168 24 32 64 128 256), losses := [] }

theorem u5416 : Upper (D 1) (R 1) [304,65,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5416
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5417_2 : Upper (D 1) (R 1) [304,65,144,160,64,2] 13 :=
  permutation_upper _ _ _ [304,65,144,160,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1895

theorem m5417_4 : Upper (D 1) (R 1) [304,65,144,160,64,4] 13 :=
  permutation_upper _ _ _ [304,65,144,160,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1897

theorem m5417_8 : Upper (D 1) (R 1) [304,65,144,160,64,8] 13 :=
  permutation_upper _ _ _ [304,65,144,160,4,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1896

def r5417 : Route 9 := (fun mask => (mask,id))

def c5417 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5417 : Upper (D 1) (R 1) [304,65,144,160,64] 13 := by
  apply FastRouting.sound _ _ [304,65,144,160,64] 13 (by decide) (choices 1) [2,4,8] r5417 c5417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5417_2
  · exact m5417_4
  · exact m5417_8

def r5418 : Route 9 := (fun mask => (mask,id))

def c5418 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5418 : Upper (D 1) (R 1) [304,65,144,192,2] 13 := by
  apply FastRouting.sound _ _ [304,65,144,192,2] 13 (by decide) (choices 1) [2,4,8] r5418 c5418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1898
  · exact u1899
  · exact u1900

def b5419 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 305 67 148 200 20 42 106 170 298), lower := (rows 305 67 148 200 20 32 64 128 256), losses := [] }

theorem u5419 : Upper (D 1) (R 1) [304,65,144,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5419
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5420 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 305 67 148 200 24 38 102 166 294), lower := (rows 305 67 148 200 24 32 64 128 256), losses := [] }

theorem u5420 : Upper (D 1) (R 1) [304,65,144,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5420
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5421 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 148 200 48 46 78 142 270), lower := (rows 305 67 148 200 48 32 64 128 256), losses := [] }

theorem u5421 : Upper (D 1) (R 1) [304,65,144,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5421
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5422 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 7 88 18 168 232 168 424), lower := (rows 305 70 7 88 18 32 64 128 256), losses := [] }

theorem u5422 : Upper (D 1) (R 1) [304,68,3,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5422
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5423 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 7 88 24 162 226 162 418), lower := (rows 305 70 7 88 24 32 64 128 256), losses := [] }

theorem u5423 : Upper (D 1) (R 1) [304,68,3,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5423
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5424 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 7 88 48 170 202 138 394), lower := (rows 305 70 7 88 48 32 64 128 256), losses := [] }

theorem u5424 : Upper (D 1) (R 1) [304,68,3,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5424
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5425 : Route 9 := (fun mask => (mask,id))

def c5425 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5425 : Upper (D 1) (R 1) [304,68,3,80,128] 13 := by
  apply FastRouting.sound _ _ [304,68,3,80,128] 13 (by decide) (choices 1) [2,8,128] r5425 c5425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1901
  · exact u1902
  · exact u1903

def b5426 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 7 152 18 232 232 232 488), lower := (rows 305 70 7 152 18 32 64 128 256), losses := [] }

theorem u5426 : Upper (D 1) (R 1) [304,68,3,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5426
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5427 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 70 7 152 24 226 226 226 482), lower := (rows 305 70 7 152 24 32 64 128 256), losses := [] }

theorem u5427 : Upper (D 1) (R 1) [304,68,3,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5427
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5428 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 7 152 48 234 202 202 458), lower := (rows 305 70 7 152 48 32 64 128 256), losses := [] }

theorem u5428 : Upper (D 1) (R 1) [304,68,3,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5428
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5429 : Route 9 := (fun mask => (mask,id))

def c5429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5429 : Upper (D 1) (R 1) [304,68,3,144,64] 13 := by
  apply FastRouting.sound _ _ [304,68,3,144,64] 13 (by decide) (choices 1) [2,8,128] r5429 c5429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1904
  · exact u1905
  · exact u1906

def b5430 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 7 152 144 106 106 234 362), lower := (rows 305 70 7 152 144 32 64 128 256), losses := [] }

theorem u5430 : Upper (D 1) (R 1) [304,68,3,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5430
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5431 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 7 200 18 184 248 184 440), lower := (rows 305 70 7 200 18 32 64 128 256), losses := [] }

theorem u5431 : Upper (D 1) (R 1) [304,68,3,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5431
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5432 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 305 70 7 200 24 178 242 178 434), lower := (rows 305 70 7 200 24 32 64 128 256), losses := [] }

theorem u5432 : Upper (D 1) (R 1) [304,68,3,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5432
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5433 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 7 200 48 186 218 154 410), lower := (rows 305 70 7 200 48 32 64 128 256), losses := [] }

theorem u5433 : Upper (D 1) (R 1) [304,68,3,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5433
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5434_2 : Upper (D 1) (R 1) [304,68,3,192,128,2] 13 :=
  permutation_upper _ _ _ [304,68,3,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1907

theorem m5434_8 : Upper (D 1) (R 1) [304,68,3,192,128,8] 13 :=
  permutation_upper _ _ _ [304,68,3,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1908

theorem m5434_16 : Upper (D 1) (R 1) [304,68,3,192,128,16] 13 :=
  permutation_upper _ _ _ [304,68,3,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1909

def r5434 : Route 9 := (fun mask => (mask,id))

def c5434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5434 : Upper (D 1) (R 1) [304,68,3,192,128] 13 := by
  apply FastRouting.sound _ _ [304,68,3,192,128] 13 (by decide) (choices 1) [2,8,16] r5434 c5434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5434_2
  · exact m5434_8
  · exact m5434_16

def b5435 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 13 138 18 240 240 240 496), lower := (rows 305 70 13 138 18 32 64 128 256), losses := [] }

theorem u5435 : Upper (D 1) (R 1) [304,68,9,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5435
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5436 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 13 138 48 242 210 210 466), lower := (rows 305 70 13 138 48 32 64 128 256), losses := [] }

theorem u5436 : Upper (D 1) (R 1) [304,68,9,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5436
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5437_2 : Upper (D 1) (R 1) [304,68,9,130,64,2] 13 :=
  permutation_upper _ _ _ [304,68,9,130,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1910

theorem m5437_16 : Upper (D 1) (R 1) [304,68,9,130,64,16] 13 :=
  permutation_upper _ _ _ [304,68,9,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1912

def r5437 : Route 9 := (fun mask => (mask,id))

def c5437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5437 : Upper (D 1) (R 1) [304,68,9,130,64] 13 := by
  apply FastRouting.sound _ _ [304,68,9,130,64] 13 (by decide) (choices 1) [2,16,128] r5437 c5437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5437_2
  · exact m5437_16
  · exact u1914

theorem m5438_2 : Upper (D 1) (R 1) [304,68,9,130,128,2] 13 :=
  permutation_upper _ _ _ [304,68,9,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1911

theorem m5438_16 : Upper (D 1) (R 1) [304,68,9,130,128,16] 13 :=
  permutation_upper _ _ _ [304,68,9,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1913

theorem m5438_64 : Upper (D 1) (R 1) [304,68,9,130,128,64] 13 :=
  permutation_upper _ _ _ [304,68,9,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1914

def r5438 : Route 9 := (fun mask => (mask,id))

def c5438 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5438 : Upper (D 1) (R 1) [304,68,9,130,128] 13 := by
  apply FastRouting.sound _ _ [304,68,9,130,128] 13 (by decide) (choices 1) [2,16,64] r5438 c5438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5438_2
  · exact m5438_16
  · exact m5438_64

def b5439 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 14 137 18 240 240 240 496), lower := (rows 305 70 14 137 18 32 64 128 256), losses := [] }

theorem u5439 : Upper (D 1) (R 1) [304,68,10,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5439
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5440 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 14 137 48 242 210 210 466), lower := (rows 305 70 14 137 48 32 64 128 256), losses := [] }

theorem u5440 : Upper (D 1) (R 1) [304,68,10,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5440
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5441_2 : Upper (D 1) (R 1) [304,68,10,129,64,2] 13 :=
  permutation_upper _ _ _ [304,68,10,129,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1915

theorem m5441_16 : Upper (D 1) (R 1) [304,68,10,129,64,16] 13 :=
  permutation_upper _ _ _ [304,68,10,129,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1917

def r5441 : Route 9 := (fun mask => (mask,id))

def c5441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5441 : Upper (D 1) (R 1) [304,68,10,129,64] 13 := by
  apply FastRouting.sound _ _ [304,68,10,129,64] 13 (by decide) (choices 1) [2,16,128] r5441 c5441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5441_2
  · exact m5441_16
  · exact u1919

theorem m5442_2 : Upper (D 1) (R 1) [304,68,10,129,128,2] 13 :=
  permutation_upper _ _ _ [304,68,10,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1916

theorem m5442_16 : Upper (D 1) (R 1) [304,68,10,129,128,16] 13 :=
  permutation_upper _ _ _ [304,68,10,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1918

theorem m5442_64 : Upper (D 1) (R 1) [304,68,10,129,128,64] 13 :=
  permutation_upper _ _ _ [304,68,10,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1919

def r5442 : Route 9 := (fun mask => (mask,id))

def c5442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5442 : Upper (D 1) (R 1) [304,68,10,129,128] 13 := by
  apply FastRouting.sound _ _ [304,68,10,129,128] 13 (by decide) (choices 1) [2,16,64] r5442 c5442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5442_2
  · exact m5442_16
  · exact m5442_64

def b5443 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 70 14 152 17 226 226 226 482), lower := (rows 305 70 14 152 17 32 64 128 256), losses := [] }

theorem u5443 : Upper (D 1) (R 1) [304,68,10,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5443
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5444 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 14 152 18 225 225 225 481), lower := (rows 305 70 14 152 18 32 64 128 256), losses := [] }

theorem u5444 : Upper (D 1) (R 1) [304,68,10,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5444
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5445 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 14 152 48 227 195 195 451), lower := (rows 305 70 14 152 48 32 64 128 256), losses := [] }

theorem u5445 : Upper (D 1) (R 1) [304,68,10,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5446 : Route 9 := (fun mask => (mask,id))

def c5446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5446 : Upper (D 1) (R 1) [304,68,10,144,64] 13 := by
  apply FastRouting.sound _ _ [304,68,10,144,64] 13 (by decide) (choices 1) [1,2,128] r5446 c5446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1920
  · exact u1921
  · exact u1922

def b5447 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 14 152 144 99 99 227 355), lower := (rows 305 70 14 152 144 32 64 128 256), losses := [] }

theorem u5447 : Upper (D 1) (R 1) [304,68,10,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5447
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5448 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 73 18 168 232 168 424), lower := (rows 305 70 22 73 18 32 64 128 256), losses := [] }

theorem u5448 : Upper (D 1) (R 1) [304,68,18,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5448
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5449 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 22 73 24 162 226 162 418), lower := (rows 305 70 22 73 24 32 64 128 256), losses := [] }

theorem u5449 : Upper (D 1) (R 1) [304,68,18,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5449
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5450 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 73 48 170 202 138 394), lower := (rows 305 70 22 73 48 32 64 128 256), losses := [] }

theorem u5450 : Upper (D 1) (R 1) [304,68,18,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5450
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5451 : Route 9 := (fun mask => (mask,id))

def c5451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5451 : Upper (D 1) (R 1) [304,68,18,65,128] 13 := by
  apply FastRouting.sound _ _ [304,68,18,65,128] 13 (by decide) (choices 1) [2,8,128] r5451 c5451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1923
  · exact u1924
  · exact u1925

def b5452 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 70 22 104 17 170 202 138 394), lower := (rows 305 70 22 104 17 32 64 128 256), losses := [] }

theorem u5452 : Upper (D 1) (R 1) [304,68,18,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5452
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5453 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 104 18 169 201 137 393), lower := (rows 305 70 22 104 18 32 64 128 256), losses := [] }

theorem u5453 : Upper (D 1) (R 1) [304,68,18,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5453
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5454 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 70 22 104 24 163 195 131 387), lower := (rows 305 70 22 104 24 32 64 128 256), losses := [] }

theorem u5454 : Upper (D 1) (R 1) [304,68,18,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5454
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5455 : Route 9 := (fun mask => (mask,id))

def c5455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5455 : Upper (D 1) (R 1) [304,68,18,96,128] 13 := by
  apply FastRouting.sound _ _ [304,68,18,96,128] 13 (by decide) (choices 1) [1,2,8,128] r5455 c5455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1926
  · exact u1927
  · exact u1928
  · exact u1929

def b5456 : PairBound 9 := { available := 232, camps := [{ cop := 6, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 137 18 232 232 232 488), lower := (rows 305 70 22 137 18 32 64 128 256), losses := [] }

theorem u5456 : Upper (D 1) (R 1) [304,68,18,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5456
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5457 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 70 22 137 24 226 226 226 482), lower := (rows 305 70 22 137 24 32 64 128 256), losses := [] }

theorem u5457 : Upper (D 1) (R 1) [304,68,18,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5457
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5458 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 137 48 234 202 202 458), lower := (rows 305 70 22 137 48 32 64 128 256), losses := [] }

theorem u5458 : Upper (D 1) (R 1) [304,68,18,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5458
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5459 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 22 137 80 170 234 170 426), lower := (rows 305 70 22 137 80 32 64 128 256), losses := [] }

theorem u5459 : Upper (D 1) (R 1) [304,68,18,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5459
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5459
end Delivery.IrregularNine14.P01
