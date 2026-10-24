import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0063
import IrregularNine14P01C0064
import IrregularNine14P01C0065

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7320 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7320 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u7320 : Upper (D 1) (R 1) [112,12,3,144] 13 := by
  apply FastRouting.sound _ _ [112,12,3,144] 13 (by decide) (choices 1) [2,32,128,256] r7320 c7320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3828
  · exact u3829
  · exact u3830
  · exact u3831

def b7321 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 7 266 240 240 240 240 496), lower := (rows 113 14 7 266 16 32 64 128 256), losses := [] }

theorem u7321 : Upper (D 1) (R 1) [112,12,3,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7321
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7322 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7322 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7322 : Upper (D 1) (R 1) [112,12,3,272] 13 := by
  apply FastRouting.sound _ _ [112,12,3,272] 13 (by decide) (choices 1) [2,32,128] r7322 c7322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3832
  · exact u3833
  · exact u3834

def r7323 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7323 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7323 : Upper (D 1) (R 1) [112,12,3,384] 13 := by
  apply FastRouting.sound _ _ [112,12,3,384] 13 (by decide) (choices 1) [2,32,128] r7323 c7323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3835
  · exact u3836
  · exact u3837

def b7324 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 21 42 466 482 450 450 450), lower := (rows 113 14 21 42 16 32 64 128 256), losses := [] }

theorem u7324 : Upper (D 1) (R 1) [112,12,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7324
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7325 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 21 138 498 482 482 482 482), lower := (rows 113 14 21 138 16 32 64 128 256), losses := [] }

theorem u7325 : Upper (D 1) (R 1) [112,12,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7325
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7326 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 21 168 466 482 450 450 450), lower := (rows 113 14 21 168 16 32 64 128 256), losses := [] }

theorem u7326 : Upper (D 1) (R 1) [112,12,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7326
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7327 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 21 266 242 226 226 226 482), lower := (rows 113 14 21 266 16 32 64 128 256), losses := [] }

theorem u7327 : Upper (D 1) (R 1) [112,12,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7327
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7328 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 21 296 210 226 194 194 450), lower := (rows 113 14 21 296 16 32 64 128 256), losses := [] }

theorem u7328 : Upper (D 1) (R 1) [112,12,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7328
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7329 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 21 392 242 226 226 226 482), lower := (rows 113 14 21 392 16 32 64 128 256), losses := [] }

theorem u7329 : Upper (D 1) (R 1) [112,12,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7329
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7330 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 22 42 465 481 449 449 449), lower := (rows 113 14 22 42 16 32 64 128 256), losses := [] }

theorem u7330 : Upper (D 1) (R 1) [112,12,18,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7330
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7331 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 113 14 22 104 403 419 451 387 387), lower := (rows 113 14 22 104 16 32 64 128 256), losses := [] }

theorem u7331 : Upper (D 1) (R 1) [112,12,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7332 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u7332 : Upper (D 1) (R 1) [112,12,18,129] 13 := by
  apply FastRouting.sound _ _ [112,12,18,129] 13 (by decide) (choices 1) [2,32,128,256] r7332 c7332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3838
  · exact u3839
  · exact u3840
  · exact u3841

def b7333 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 22 138 497 481 481 481 481), lower := (rows 113 14 22 138 16 32 64 128 256), losses := [] }

theorem u7333 : Upper (D 1) (R 1) [112,12,18,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7333
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7334 : Route 9 := (fun mask => (mask,id))

def c7334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u7334 : Upper (D 1) (R 1) [112,12,18,160] 13 := by
  apply FastRouting.sound _ _ [112,12,18,160] 13 (by decide) (choices 1) [1,2,64,128,256] r7334 c7334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3842
  · exact u3843
  · exact u3844
  · exact u3845
  · exact u3846

def r7335 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7335 : Upper (D 1) (R 1) [112,12,18,257] 13 := by
  apply FastRouting.sound _ _ [112,12,18,257] 13 (by decide) (choices 1) [2,32,128] r7335 c7335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3847
  · exact u3848
  · exact u3849

def b7336 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 22 266 241 225 225 225 481), lower := (rows 113 14 22 266 16 32 64 128 256), losses := [] }

theorem u7336 : Upper (D 1) (R 1) [112,12,18,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7336
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7337 : Route 9 := (fun mask => (mask,id))

def c7337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7337 : Upper (D 1) (R 1) [112,12,18,288] 13 := by
  apply FastRouting.sound _ _ [112,12,18,288] 13 (by decide) (choices 1) [1,2,64,128] r7337 c7337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3850
  · exact u3851
  · exact u3852
  · exact u3853

def r7338 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7338 : Upper (D 1) (R 1) [112,12,18,384] 13 := by
  apply FastRouting.sound _ _ [112,12,18,384] 13 (by decide) (choices 1) [1,2,32,128] r7338 c7338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3854
  · exact u3855
  · exact u3856
  · exact u3857

def b7339 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 52 137 466 482 450 450 450), lower := (rows 113 14 52 137 16 32 64 128 256), losses := [] }

theorem u7339 : Upper (D 1) (R 1) [112,12,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7339
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7340 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 52 138 467 483 451 451 451), lower := (rows 113 14 52 138 16 32 64 128 256), losses := [] }

theorem u7340 : Upper (D 1) (R 1) [112,12,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7340
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7341 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 52 200 403 419 451 387 387), lower := (rows 113 14 52 200 16 32 64 128 256), losses := [] }

theorem u7341 : Upper (D 1) (R 1) [112,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7341
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7342 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 52 265 210 226 194 194 450), lower := (rows 113 14 52 265 16 32 64 128 256), losses := [] }

theorem u7342 : Upper (D 1) (R 1) [112,12,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7342
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7343 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 52 266 211 227 195 195 451), lower := (rows 113 14 52 266 16 32 64 128 256), losses := [] }

theorem u7343 : Upper (D 1) (R 1) [112,12,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7343
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7344 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 52 328 147 163 195 131 387), lower := (rows 113 14 52 328 16 32 64 128 256), losses := [] }

theorem u7344 : Upper (D 1) (R 1) [112,12,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7344
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7345 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 52 392 211 227 195 195 451), lower := (rows 113 14 52 392 16 32 64 128 256), losses := [] }

theorem u7345 : Upper (D 1) (R 1) [112,12,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7346 : PairBound 9 := { available := 370, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 133 138 370 370 370 498 370), lower := (rows 113 14 133 138 16 32 64 128 256), losses := [] }

theorem u7346 : Upper (D 1) (R 1) [112,12,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7346
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7347 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 133 152 370 354 354 482 354), lower := (rows 113 14 133 152 16 32 64 128 256), losses := [] }

theorem u7347 : Upper (D 1) (R 1) [112,12,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7347
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7348 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7348 : Upper (D 1) (R 1) [112,12,129,258] 13 := by
  apply FastRouting.sound _ _ [112,12,129,258] 13 (by decide) (choices 1) [2,32,128] r7348 c7348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3858
  · exact u3859
  · exact u3860

def r7349 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7349 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7349 : Upper (D 1) (R 1) [112,12,129,272] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272] 13 (by decide) (choices 1) [2,32,128] r7349 c7349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3861
  · exact u3862
  · exact u3863

def b7350 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 133 392 114 114 114 242 370), lower := (rows 113 14 133 392 16 32 64 128 256), losses := [] }

theorem u7350 : Upper (D 1) (R 1) [112,12,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7350
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7351 : PairBound 9 := { available := 369, camps := [{ cop := 7, region := 14, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 134 138 369 369 369 497 369), lower := (rows 113 14 134 138 16 32 64 128 256), losses := [] }

theorem u7351 : Upper (D 1) (R 1) [112,12,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7351
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7352 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 134 152 371 355 355 483 355), lower := (rows 113 14 134 152 16 32 64 128 256), losses := [] }

theorem u7352 : Upper (D 1) (R 1) [112,12,130,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7352
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7353 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7353 : Upper (D 1) (R 1) [112,12,130,257] 13 := by
  apply FastRouting.sound _ _ [112,12,130,257] 13 (by decide) (choices 1) [2,32,128] r7353 c7353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3864
  · exact u3865
  · exact u3866

def b7354 : PairBound 9 := { available := 241, camps := [{ cop := 1, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 134 266 241 241 241 241 497), lower := (rows 113 14 134 266 16 32 64 128 256), losses := [] }

theorem u7354 : Upper (D 1) (R 1) [112,12,130,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7354
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7355 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7355 : Upper (D 1) (R 1) [112,12,130,272] 13 := by
  apply FastRouting.sound _ _ [112,12,130,272] 13 (by decide) (choices 1) [1,2,32,128] r7355 c7355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3867
  · exact u3868
  · exact u3869
  · exact u3870

def b7356 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 134 392 115 115 115 243 371), lower := (rows 113 14 134 392 16 32 64 128 256), losses := [] }

theorem u7356 : Upper (D 1) (R 1) [112,12,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7356
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7357 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 168 339 355 323 451 323), lower := (rows 113 14 148 168 16 32 64 128 256), losses := [] }

theorem u7357 : Upper (D 1) (R 1) [112,12,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7357
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7358 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7358 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7358 : Upper (D 1) (R 1) [112,12,144,257] 13 := by
  apply FastRouting.sound _ _ [112,12,144,257] 13 (by decide) (choices 1) [2,32,128] r7358 c7358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3871
  · exact u3872
  · exact u3873

def r7359 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7359 : Upper (D 1) (R 1) [112,12,144,258] 13 := by
  apply FastRouting.sound _ _ [112,12,144,258] 13 (by decide) (choices 1) [1,2,32,128] r7359 c7359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3874
  · exact u3875
  · exact u3876
  · exact u3877

def r7360 : Route 9 := (fun mask => (mask,id))

def c7360 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7360 : Upper (D 1) (R 1) [112,12,144,288] 13 := by
  apply FastRouting.sound _ _ [112,12,144,288] 13 (by decide) (choices 1) [1,2,64,128] r7360 c7360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3878
  · exact u3879
  · exact u3880
  · exact u3881

def b7361 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 392 115 99 99 227 355), lower := (rows 113 14 148 392 16 32 64 128 256), losses := [] }

theorem u7361 : Upper (D 1) (R 1) [112,12,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7361
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7362 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 14 11 496 480 480 480 480), lower := (rows 113 22 14 11 16 32 64 128 256), losses := [] }

theorem u7362 : Upper (D 1) (R 1) [112,20,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7362
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7363 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 14 41 466 482 450 450 450), lower := (rows 113 22 14 41 16 32 64 128 256), losses := [] }

theorem u7363 : Upper (D 1) (R 1) [112,20,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7363
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7364 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 14 42 465 481 449 449 449), lower := (rows 113 22 14 42 16 32 64 128 256), losses := [] }

theorem u7364 : Upper (D 1) (R 1) [112,20,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7364
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7365 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 14 104 403 419 451 387 387), lower := (rows 113 22 14 104 16 32 64 128 256), losses := [] }

theorem u7365 : Upper (D 1) (R 1) [112,20,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7365
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7366 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7366 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u7366 : Upper (D 1) (R 1) [112,20,10,129] 13 := by
  apply FastRouting.sound _ _ [112,20,10,129] 13 (by decide) (choices 1) [2,32,128,256] r7366 c7366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3882
  · exact u3883
  · exact u3884
  · exact u3885

def b7367 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 14 138 497 481 481 481 481), lower := (rows 113 22 14 138 16 32 64 128 256), losses := [] }

theorem u7367 : Upper (D 1) (R 1) [112,20,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7367
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7368 : Route 9 := (fun mask => (mask,id))

def c7368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u7368 : Upper (D 1) (R 1) [112,20,10,160] 13 := by
  apply FastRouting.sound _ _ [112,20,10,160] 13 (by decide) (choices 1) [1,2,64,128,256] r7368 c7368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3886
  · exact u3887
  · exact u3888
  · exact u3889
  · exact u3890

def r7369 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7369 : Upper (D 1) (R 1) [112,20,10,257] 13 := by
  apply FastRouting.sound _ _ [112,20,10,257] 13 (by decide) (choices 1) [2,32,128] r7369 c7369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3891
  · exact u3892
  · exact u3893

def b7370 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 14 266 241 225 225 225 481), lower := (rows 113 22 14 266 16 32 64 128 256), losses := [] }

theorem u7370 : Upper (D 1) (R 1) [112,20,10,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7370
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7371 : Route 9 := (fun mask => (mask,id))

def c7371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7371 : Upper (D 1) (R 1) [112,20,10,288] 13 := by
  apply FastRouting.sound _ _ [112,20,10,288] 13 (by decide) (choices 1) [1,2,64,128] r7371 c7371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3894
  · exact u3895
  · exact u3896
  · exact u3897

def r7372 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7372 : Upper (D 1) (R 1) [112,20,10,384] 13 := by
  apply FastRouting.sound _ _ [112,20,10,384] 13 (by decide) (choices 1) [1,2,32,128] r7372 c7372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3898
  · exact u3899
  · exact u3900
  · exact u3901

def b7373 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 11 466 482 450 450 450), lower := (rows 113 22 44 11 16 32 64 128 256), losses := [] }

theorem u7373 : Upper (D 1) (R 1) [112,20,40,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7373
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7374 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 22 44 73 402 418 450 386 386), lower := (rows 113 22 44 73 16 32 64 128 256), losses := [] }

theorem u7374 : Upper (D 1) (R 1) [112,20,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7374
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7375 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 44 74 403 419 451 387 387), lower := (rows 113 22 44 74 16 32 64 128 256), losses := [] }

theorem u7375 : Upper (D 1) (R 1) [112,20,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7375
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7376 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 137 466 482 450 450 450), lower := (rows 113 22 44 137 16 32 64 128 256), losses := [] }

theorem u7376 : Upper (D 1) (R 1) [112,20,40,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7376
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7377 : Route 9 := (fun mask => (mask,id))

def c7377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u7377 : Upper (D 1) (R 1) [112,20,40,130] 13 := by
  apply FastRouting.sound _ _ [112,20,40,130] 13 (by decide) (choices 1) [1,2,64,128,256] r7377 c7377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3902
  · exact u3903
  · exact u3904
  · exact u3905
  · exact u3906

def r7378 : Route 9 := (fun mask => (mask,id))

def c7378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u7378 : Upper (D 1) (R 1) [112,20,40,192] 13 := by
  apply FastRouting.sound _ _ [112,20,40,192] 13 (by decide) (choices 1) [1,2,128,256] r7378 c7378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3907
  · exact u3908
  · exact u3909
  · exact u3910

def b7379 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 265 210 226 194 194 450), lower := (rows 113 22 44 265 16 32 64 128 256), losses := [] }

theorem u7379 : Upper (D 1) (R 1) [112,20,40,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7379
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7379
end Delivery.IrregularNine14.P01
