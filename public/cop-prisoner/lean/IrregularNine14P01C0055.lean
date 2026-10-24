import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0013

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3300 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 74 388 26 17 226 226 226 482), lower := (rows 53 74 388 26 17 32 64 128 256), losses := [] }

theorem u3300 : Upper (D 1) (R 1) [52,72,384,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3300
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3301 : PairBound 9 := { available := 225, camps := [{ cop := 6, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 388 26 18 225 225 225 481), lower := (rows 53 74 388 26 18 32 64 128 256), losses := [] }

theorem u3301 : Upper (D 1) (R 1) [52,72,384,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3302 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 388 26 48 227 195 195 451), lower := (rows 53 74 388 26 48 32 64 128 256), losses := [] }

theorem u3302 : Upper (D 1) (R 1) [52,72,384,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3302
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3303 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 388 26 80 163 227 163 419), lower := (rows 53 74 388 26 80 32 64 128 256), losses := [] }

theorem u3303 : Upper (D 1) (R 1) [52,72,384,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3303
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3304 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 388 26 144 99 99 227 355), lower := (rows 53 74 388 26 144 32 64 128 256), losses := [] }

theorem u3304 : Upper (D 1) (R 1) [52,72,384,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3304
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3305 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 53 74 388 138 17 114 114 242 370), lower := (rows 53 74 388 138 17 32 64 128 256), losses := [] }

theorem u3305 : Upper (D 1) (R 1) [52,72,384,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3305
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3306 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 388 138 18 113 113 241 369), lower := (rows 53 74 388 138 18 32 64 128 256), losses := [] }

theorem u3306 : Upper (D 1) (R 1) [52,72,384,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3307 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 388 138 48 115 83 211 339), lower := (rows 53 74 388 138 48 32 64 128 256), losses := [] }

theorem u3307 : Upper (D 1) (R 1) [52,72,384,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3307
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3308_1 : Upper (D 1) (R 1) [52,72,384,130,64,1] 13 :=
  permutation_upper _ _ _ [52,72,384,130,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u821

theorem m3308_2 : Upper (D 1) (R 1) [52,72,384,130,64,2] 13 :=
  permutation_upper _ _ _ [52,72,384,130,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u822

theorem m3308_16 : Upper (D 1) (R 1) [52,72,384,130,64,16] 13 :=
  permutation_upper _ _ _ [52,72,384,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u823

def r3308 : Route 9 := (fun mask => (mask,id))

def c3308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3308 : Upper (D 1) (R 1) [52,72,384,130,64] 13 := by
  apply FastRouting.sound _ _ [52,72,384,130,64] 13 (by decide) (choices 1) [1,2,16] r3308 c3308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3308_1
  · exact m3308_2
  · exact m3308_16

def b3309 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 53 74 388 152 17 98 98 226 354), lower := (rows 53 74 388 152 17 32 64 128 256), losses := [] }

theorem u3309 : Upper (D 1) (R 1) [52,72,384,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3309
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3310 : Route 9 := (fun mask => (mask,id))

def c3310 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3310 : Upper (D 1) (R 1) [52,72,384,144,2] 13 := by
  apply FastRouting.sound _ _ [52,72,384,144,2] 13 (by decide) (choices 1) [1,2,64] r3310 c3310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u824
  · exact u825
  · exact u826

def b3311 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 388 152 48 99 67 195 323), lower := (rows 53 74 388 152 48 32 64 128 256), losses := [] }

theorem u3311 : Upper (D 1) (R 1) [52,72,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3311
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3312 : Route 9 := (fun mask => (mask,id))

def c3312 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3312 : Upper (D 1) (R 1) [52,72,384,144,64] 13 := by
  apply FastRouting.sound _ _ [52,72,384,144,64] 13 (by decide) (choices 1) [1,2] r3312 c3312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u827
  · exact u828

def b3313 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 82 14 392 17 226 226 226 482), lower := (rows 53 82 14 392 17 32 64 128 256), losses := [] }

theorem u3313 : Upper (D 1) (R 1) [52,80,10,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3313
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3314 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 14 392 18 225 225 225 481), lower := (rows 53 82 14 392 18 32 64 128 256), losses := [] }

theorem u3314 : Upper (D 1) (R 1) [52,80,10,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3314
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3315 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 14 392 48 227 195 195 451), lower := (rows 53 82 14 392 48 32 64 128 256), losses := [] }

theorem u3315 : Upper (D 1) (R 1) [52,80,10,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3315
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3316 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 14 392 80 163 227 163 419), lower := (rows 53 82 14 392 80 32 64 128 256), losses := [] }

theorem u3316 : Upper (D 1) (R 1) [52,80,10,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3316
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3317 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 14 392 144 99 99 227 355), lower := (rows 53 82 14 392 144 32 64 128 256), losses := [] }

theorem u3317 : Upper (D 1) (R 1) [52,80,10,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3317
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3318 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 137 18 418 482 418 418), lower := (rows 53 82 76 137 18 32 64 128 256), losses := [] }

theorem u3318 : Upper (D 1) (R 1) [52,80,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3318
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3319 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 137 48 418 450 386 386), lower := (rows 53 82 76 137 48 32 64 128 256), losses := [] }

theorem u3319 : Upper (D 1) (R 1) [52,80,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3319
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3320 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 76 137 144 290 354 418 290), lower := (rows 53 82 76 137 144 32 64 128 256), losses := [] }

theorem u3320 : Upper (D 1) (R 1) [52,80,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3320
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3321 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 76 137 272 162 226 162 418), lower := (rows 53 82 76 137 272 32 64 128 256), losses := [] }

theorem u3321 : Upper (D 1) (R 1) [52,80,72,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3321
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3322 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 53 82 76 138 17 418 482 418 418), lower := (rows 53 82 76 138 17 32 64 128 256), losses := [] }

theorem u3322 : Upper (D 1) (R 1) [52,80,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3322
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3323 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 138 18 417 481 417 417), lower := (rows 53 82 76 138 18 32 64 128 256), losses := [] }

theorem u3323 : Upper (D 1) (R 1) [52,80,72,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3323
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3324 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 138 48 419 451 387 387), lower := (rows 53 82 76 138 48 32 64 128 256), losses := [] }

theorem u3324 : Upper (D 1) (R 1) [52,80,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3324
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3325 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 76 138 144 291 355 419 291), lower := (rows 53 82 76 138 144 32 64 128 256), losses := [] }

theorem u3325 : Upper (D 1) (R 1) [52,80,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3325
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3326 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 82 76 138 272 163 227 163 419), lower := (rows 53 82 76 138 272 32 64 128 256), losses := [] }

theorem u3326 : Upper (D 1) (R 1) [52,80,72,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3326
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3327 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 265 18 162 226 162 418), lower := (rows 53 82 76 265 18 32 64 128 256), losses := [] }

theorem u3327 : Upper (D 1) (R 1) [52,80,72,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3327
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3328 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 265 48 162 194 130 386), lower := (rows 53 82 76 265 48 32 64 128 256), losses := [] }

theorem u3328 : Upper (D 1) (R 1) [52,80,72,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3328
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3329 : Route 9 := (fun mask => (mask,id))

def c3329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3329 : Upper (D 1) (R 1) [52,80,72,257,128] 13 := by
  apply FastRouting.sound _ _ [52,80,72,257,128] 13 (by decide) (choices 1) [2,128] r3329 c3329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u829
  · exact u830

def b3330 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 76 266 17 162 226 162 418), lower := (rows 53 82 76 266 17 32 64 128 256), losses := [] }

theorem u3330 : Upper (D 1) (R 1) [52,80,72,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3330
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3331 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 266 18 161 225 161 417), lower := (rows 53 82 76 266 18 32 64 128 256), losses := [] }

theorem u3331 : Upper (D 1) (R 1) [52,80,72,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3332 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 266 48 163 195 131 387), lower := (rows 53 82 76 266 48 32 64 128 256), losses := [] }

theorem u3332 : Upper (D 1) (R 1) [52,80,72,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3332
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3333 : Route 9 := (fun mask => (mask,id))

def c3333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3333 : Upper (D 1) (R 1) [52,80,72,258,128] 13 := by
  apply FastRouting.sound _ _ [52,80,72,258,128] 13 (by decide) (choices 1) [1,2,128] r3333 c3333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u831
  · exact u832
  · exact u833

def b3334 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 76 392 17 162 226 162 418), lower := (rows 53 82 76 392 17 32 64 128 256), losses := [] }

theorem u3334 : Upper (D 1) (R 1) [52,80,72,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3334
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3335 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 392 18 163 227 163 419), lower := (rows 53 82 76 392 18 32 64 128 256), losses := [] }

theorem u3335 : Upper (D 1) (R 1) [52,80,72,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3335
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3336 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 76 392 48 163 195 131 387), lower := (rows 53 82 76 392 48 32 64 128 256), losses := [] }

theorem u3336 : Upper (D 1) (R 1) [52,80,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3336
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3337 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 76 392 144 35 99 163 291), lower := (rows 53 82 76 392 144 32 64 128 256), losses := [] }

theorem u3337 : Upper (D 1) (R 1) [52,80,72,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3337
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3338 : PairBound 9 := { available := 456, camps := [], pairs := [], upper := (rows 53 82 134 42 17 488 456 456 456), lower := (rows 53 82 134 42 17 32 64 128 256), losses := [] }

theorem u3338 : Upper (D 1) (R 1) [52,80,130,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3338
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3339 : PairBound 9 := { available := 449, camps := [], pairs := [], upper := (rows 53 82 134 42 24 481 449 449 449), lower := (rows 53 82 134 42 24 32 64 128 256), losses := [] }

theorem u3339 : Upper (D 1) (R 1) [52,80,130,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3339
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3340 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 134 42 80 425 457 393 393), lower := (rows 53 82 134 42 80 32 64 128 256), losses := [] }

theorem u3340 : Upper (D 1) (R 1) [52,80,130,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3340
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3341 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 134 42 144 361 329 457 329), lower := (rows 53 82 134 42 144 32 64 128 256), losses := [] }

theorem u3341 : Upper (D 1) (R 1) [52,80,130,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3341
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3342 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 53 82 134 42 272 233 201 201 457), lower := (rows 53 82 134 42 272 32 64 128 256), losses := [] }

theorem u3342 : Upper (D 1) (R 1) [52,80,130,34,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3342
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3343 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 134 73 18 424 488 424 424), lower := (rows 53 82 134 73 18 32 64 128 256), losses := [] }

theorem u3343 : Upper (D 1) (R 1) [52,80,130,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3343
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3344 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 53 82 134 73 24 418 482 418 418), lower := (rows 53 82 134 73 24 32 64 128 256), losses := [] }

theorem u3344 : Upper (D 1) (R 1) [52,80,130,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3344
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3345 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 134 73 48 426 458 394 394), lower := (rows 53 82 134 73 48 32 64 128 256), losses := [] }

theorem u3345 : Upper (D 1) (R 1) [52,80,130,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3346 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 134 73 144 298 362 426 298), lower := (rows 53 82 134 73 144 32 64 128 256), losses := [] }

theorem u3346 : Upper (D 1) (R 1) [52,80,130,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3346
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3347 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 82 134 73 272 170 234 170 426), lower := (rows 53 82 134 73 272 32 64 128 256), losses := [] }

theorem u3347 : Upper (D 1) (R 1) [52,80,130,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3347
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3348 : PairBound 9 := { available := 394, camps := [], pairs := [], upper := (rows 53 82 134 104 17 426 458 394 394), lower := (rows 53 82 134 104 17 32 64 128 256), losses := [] }

theorem u3348 : Upper (D 1) (R 1) [52,80,130,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3348
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3349 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 134 104 18 425 457 393 393), lower := (rows 53 82 134 104 18 32 64 128 256), losses := [] }

theorem u3349 : Upper (D 1) (R 1) [52,80,130,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3349
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3350 : PairBound 9 := { available := 387, camps := [], pairs := [], upper := (rows 53 82 134 104 24 419 451 387 387), lower := (rows 53 82 134 104 24 32 64 128 256), losses := [] }

theorem u3350 : Upper (D 1) (R 1) [52,80,130,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3350
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3351 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 134 104 144 299 331 395 267), lower := (rows 53 82 134 104 144 32 64 128 256), losses := [] }

theorem u3351 : Upper (D 1) (R 1) [52,80,130,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3351
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3352 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 53 82 134 104 272 171 203 139 395), lower := (rows 53 82 134 104 272 32 64 128 256), losses := [] }

theorem u3352 : Upper (D 1) (R 1) [52,80,130,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3352
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3353 : PairBound 9 := { available := 330, camps := [], pairs := [], upper := (rows 53 82 134 168 17 362 330 458 330), lower := (rows 53 82 134 168 17 32 64 128 256), losses := [] }

theorem u3353 : Upper (D 1) (R 1) [52,80,130,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3353
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3354 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 134 168 18 361 329 457 329), lower := (rows 53 82 134 168 18 32 64 128 256), losses := [] }

theorem u3354 : Upper (D 1) (R 1) [52,80,130,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3354
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3355 : PairBound 9 := { available := 323, camps := [], pairs := [], upper := (rows 53 82 134 168 24 355 323 451 323), lower := (rows 53 82 134 168 24 32 64 128 256), losses := [] }

theorem u3355 : Upper (D 1) (R 1) [52,80,130,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3355
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3356 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 134 168 80 299 331 395 267), lower := (rows 53 82 134 168 80 32 64 128 256), losses := [] }

theorem u3356 : Upper (D 1) (R 1) [52,80,130,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3356
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3357 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 53 82 134 168 272 107 75 203 331), lower := (rows 53 82 134 168 272 32 64 128 256), losses := [] }

theorem u3357 : Upper (D 1) (R 1) [52,80,130,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3357
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3358 : PairBound 9 := { available := 298, camps := [], pairs := [], upper := (rows 53 82 134 200 17 298 362 426 298), lower := (rows 53 82 134 200 17 32 64 128 256), losses := [] }

theorem u3358 : Upper (D 1) (R 1) [52,80,130,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3358
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3359 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 134 200 18 297 361 425 297), lower := (rows 53 82 134 200 18 32 64 128 256), losses := [] }

theorem u3359 : Upper (D 1) (R 1) [52,80,130,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3359
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3359
end Delivery.IrregularNine14.P01
