import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0062
import IrregularNine14P05C0063

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7320 : PairBound 9 := { available := 300, camps := [], pairs := [(2,0),(4,0)], upper := (rows 19 67 38 137 28 300 364 428 300), lower := (rows 19 67 38 137 28 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 24 56 88 152 280), good := (rows 502 70 38 508 508 32 64 128 256) }] }

theorem u7320 : Upper (D 5) (R 5) [18,65,34,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7320
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7321 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 38 137 52 300 332 396 268), lower := (rows 19 67 38 137 52 32 64 128 256), losses := [] }

theorem u7321 : Upper (D 5) (R 5) [18,65,34,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7321
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7322 : Route 9 := (fun mask => (mask,id))

def c7322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7322 : Upper (D 5) (R 5) [18,65,34,129,40] 13 := by
  apply FastRouting.sound _ _ [18,65,34,129,40] 13 (by decide) (choices 1) [4,8,256] r7322 c7322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3749
  · exact u3750
  · exact u3751

def r7323 : Route 9 := (fun mask => (mask,id))

def c7323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7323 : Upper (D 5) (R 5) [18,65,34,129,260] 13 := by
  apply FastRouting.sound _ _ [18,65,34,129,260] 13 (by decide) (choices 1) [4,8] r7323 c7323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3752
  · exact u3753

def r7324 : Route 9 := (fun mask => (mask,id))

def c7324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7324 : Upper (D 5) (R 5) [18,65,34,129,264] 13 := by
  apply FastRouting.sound _ _ [18,65,34,129,264] 13 (by decide) (choices 1) [4,8] r7324 c7324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3754
  · exact u3755

def r7325 : Route 9 := (fun mask => (mask,id))

def c7325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7325 : Upper (D 5) (R 5) [18,65,34,129,288] 13 := by
  apply FastRouting.sound _ _ [18,65,34,129,288] 13 (by decide) (choices 1) [4,8] r7325 c7325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3756
  · exact u3757

def b7326 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 38 140 21 296 360 424 296), lower := (rows 19 67 38 140 21 32 64 128 256), losses := [] }

theorem u7326 : Upper (D 5) (R 5) [18,65,34,132,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7326
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7327 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 38 140 25 300 364 428 300), lower := (rows 19 67 38 140 25 32 64 128 256), losses := [] }

theorem u7327 : Upper (D 5) (R 5) [18,65,34,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7327
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7328 : PairBound 9 := { available := 297, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 38 140 28 297 361 425 297), lower := (rows 19 67 38 140 28 32 64 128 256), losses := [] }

theorem u7328 : Upper (D 5) (R 5) [18,65,34,132,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7328
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7329 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 38 140 49 300 332 396 268), lower := (rows 19 67 38 140 49 32 64 128 256), losses := [] }

theorem u7329 : Upper (D 5) (R 5) [18,65,34,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7329
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7330 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 38 140 52 297 329 393 265), lower := (rows 19 67 38 140 52 32 64 128 256), losses := [] }

theorem u7330 : Upper (D 5) (R 5) [18,65,34,132,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7330
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7331 : Route 9 := (fun mask => (mask,id))

def c7331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7331 : Upper (D 5) (R 5) [18,65,34,132,40] 13 := by
  apply FastRouting.sound _ _ [18,65,34,132,40] 13 (by decide) (choices 1) [1,4,8,256] r7331 c7331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3758
  · exact u3759
  · exact u3760
  · exact u3761

def b7332 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 172, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 38 140 273 44 108 172 300), lower := (rows 19 67 38 140 273 32 64 128 256), losses := [] }

theorem u7332 : Upper (D 5) (R 5) [18,65,34,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7332
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7333 : Route 9 := (fun mask => (mask,id))

def c7333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7333 : Upper (D 5) (R 5) [18,65,34,132,260] 13 := by
  apply FastRouting.sound _ _ [18,65,34,132,260] 13 (by decide) (choices 1) [1,8] r7333 c7333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3762
  · exact u3763

def r7334 : Route 9 := (fun mask => (mask,id))

def c7334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7334 : Upper (D 5) (R 5) [18,65,34,132,264] 13 := by
  apply FastRouting.sound _ _ [18,65,34,132,264] 13 (by decide) (choices 1) [1,4,8] r7334 c7334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3764
  · exact u3765
  · exact u3766

def r7335 : Route 9 := (fun mask => (mask,id))

def c7335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7335 : Upper (D 5) (R 5) [18,65,34,132,288] 13 := by
  apply FastRouting.sound _ _ [18,65,34,132,288] 13 (by decide) (choices 1) [1,4,8] r7335 c7335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3767
  · exact u3768
  · exact u3769

def b7336 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 38 168 21 300 332 396 268), lower := (rows 19 67 38 168 21 32 64 128 256), losses := [] }

theorem u7336 : Upper (D 5) (R 5) [18,65,34,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7336
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7337 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 38 168 25 300 332 396 268), lower := (rows 19 67 38 168 25 32 64 128 256), losses := [] }

theorem u7337 : Upper (D 5) (R 5) [18,65,34,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7337
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7338 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 38 168 28 301 333 397 269), lower := (rows 19 67 38 168 28 32 64 128 256), losses := [] }

theorem u7338 : Upper (D 5) (R 5) [18,65,34,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7338
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7339 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 172, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 38 168 273 44 76 140 268), lower := (rows 19 67 38 168 273 32 64 128 256), losses := [] }

theorem u7339 : Upper (D 5) (R 5) [18,65,34,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7339
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7340 : Route 9 := (fun mask => (mask,id))

def c7340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7340 : Upper (D 5) (R 5) [18,65,34,160,260] 13 := by
  apply FastRouting.sound _ _ [18,65,34,160,260] 13 (by decide) (choices 1) [1,4,8] r7340 c7340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3770
  · exact u3771
  · exact u3772

def r7341 : Route 9 := (fun mask => (mask,id))

def c7341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7341 : Upper (D 5) (R 5) [18,65,34,160,264] 13 := by
  apply FastRouting.sound _ _ [18,65,34,160,264] 13 (by decide) (choices 1) [1,4,8] r7341 c7341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3773
  · exact u3774
  · exact u3775

def b7342 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 38 392 21 44 108 172 300), lower := (rows 19 67 38 392 21 32 64 128 256), losses := [] }

theorem u7342 : Upper (D 5) (R 5) [18,65,34,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7342
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7343 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 38 392 25 44 108 172 300), lower := (rows 19 67 38 392 25 32 64 128 256), losses := [] }

theorem u7343 : Upper (D 5) (R 5) [18,65,34,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7343
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7344 : Route 9 := (fun mask => (mask,id))

def c7344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7344 : Upper (D 5) (R 5) [18,65,34,384,12] 13 := by
  apply FastRouting.sound _ _ [18,65,34,384,12] 13 (by decide) (choices 1) [1,4,8] r7344 c7344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3776
  · exact u3777
  · exact u3778

def b7345 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 38 392 49 44 76 140 268), lower := (rows 19 67 38 392 49 32 64 128 256), losses := [] }

theorem u7345 : Upper (D 5) (R 5) [18,65,34,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7345
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7346 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 38 392 52 45 77 141 269), lower := (rows 19 67 38 392 52 32 64 128 256), losses := [] }

theorem u7346 : Upper (D 5) (R 5) [18,65,34,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7346
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7347 : Route 9 := (fun mask => (mask,id))

def c7347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7347 : Upper (D 5) (R 5) [18,65,34,384,40] 13 := by
  apply FastRouting.sound _ _ [18,65,34,384,40] 13 (by decide) (choices 1) [1,4,8] r7347 c7347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3779
  · exact u3780
  · exact u3781

def b7348 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 137 22 300 364 428 300), lower := (rows 19 67 44 137 22 32 64 128 256), losses := [] }

theorem u7348 : Upper (D 5) (R 5) [18,65,40,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7348
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7349 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 137 26 292 356 420 292), lower := (rows 19 67 44 137 26 32 64 128 256), losses := [] }

theorem u7349 : Upper (D 5) (R 5) [18,65,40,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7349
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7350 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 137 28 294 358 422 294), lower := (rows 19 67 44 137 28 32 64 128 256), losses := [] }

theorem u7350 : Upper (D 5) (R 5) [18,65,40,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7350
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7351 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 137 50 300 332 396 268), lower := (rows 19 67 44 137 50 32 64 128 256), losses := [] }

theorem u7351 : Upper (D 5) (R 5) [18,65,40,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7351
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7352 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 137 52 302 334 398 270), lower := (rows 19 67 44 137 52 32 64 128 256), losses := [] }

theorem u7352 : Upper (D 5) (R 5) [18,65,40,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7352
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7353 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 137 56 294 326 390 262), lower := (rows 19 67 44 137 56 32 64 128 256), losses := [] }

theorem u7353 : Upper (D 5) (R 5) [18,65,40,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7353
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7354 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 137 274 44 108 172 300), lower := (rows 19 67 44 137 274 32 64 128 256), losses := [] }

theorem u7354 : Upper (D 5) (R 5) [18,65,40,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7354
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7355 : Route 9 := (fun mask => (mask,id))

def c7355 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7355 : Upper (D 5) (R 5) [18,65,40,129,260] 13 := by
  apply FastRouting.sound _ _ [18,65,40,129,260] 13 (by decide) (choices 1) [2,4,8] r7355 c7355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3782
  · exact u3783
  · exact u3784

def r7356 : Route 9 := (fun mask => (mask,id))

def c7356 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7356 : Upper (D 5) (R 5) [18,65,40,129,264] 13 := by
  apply FastRouting.sound _ _ [18,65,40,129,264] 13 (by decide) (choices 1) [2,4] r7356 c7356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3785
  · exact u3786

def r7357 : Route 9 := (fun mask => (mask,id))

def c7357 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7357 : Upper (D 5) (R 5) [18,65,40,129,288] 13 := by
  apply FastRouting.sound _ _ [18,65,40,129,288] 13 (by decide) (choices 1) [2,4,8] r7357 c7357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3787
  · exact u3788
  · exact u3789

def b7358 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 138 21 300 364 428 300), lower := (rows 19 67 44 138 21 32 64 128 256), losses := [] }

theorem u7358 : Upper (D 5) (R 5) [18,65,40,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7358
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7359 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 67 44 138 25 292 356 420 292), lower := (rows 19 67 44 138 25 32 64 128 256), losses := [] }

theorem u7359 : Upper (D 5) (R 5) [18,65,40,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7359
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7360 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 138 28 293 357 421 293), lower := (rows 19 67 44 138 28 32 64 128 256), losses := [] }

theorem u7360 : Upper (D 5) (R 5) [18,65,40,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7360
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7361 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 138 49 300 332 396 268), lower := (rows 19 67 44 138 49 32 64 128 256), losses := [] }

theorem u7361 : Upper (D 5) (R 5) [18,65,40,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7361
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7362 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 138 52 301 333 397 269), lower := (rows 19 67 44 138 52 32 64 128 256), losses := [] }

theorem u7362 : Upper (D 5) (R 5) [18,65,40,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7362
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7363 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 138 56 293 325 389 261), lower := (rows 19 67 44 138 56 32 64 128 256), losses := [] }

theorem u7363 : Upper (D 5) (R 5) [18,65,40,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7363
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7364 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 172, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 138 273 44 108 172 300), lower := (rows 19 67 44 138 273 32 64 128 256), losses := [] }

theorem u7364 : Upper (D 5) (R 5) [18,65,40,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7364
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7365 : Route 9 := (fun mask => (mask,id))

def c7365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7365 : Upper (D 5) (R 5) [18,65,40,130,260] 13 := by
  apply FastRouting.sound _ _ [18,65,40,130,260] 13 (by decide) (choices 1) [1,4,8] r7365 c7365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3790
  · exact u3791
  · exact u3792

def r7366 : Route 9 := (fun mask => (mask,id))

def c7366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7366 : Upper (D 5) (R 5) [18,65,40,130,264] 13 := by
  apply FastRouting.sound _ _ [18,65,40,130,264] 13 (by decide) (choices 1) [1,4] r7366 c7366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3793
  · exact u3794

def r7367 : Route 9 := (fun mask => (mask,id))

def c7367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7367 : Upper (D 5) (R 5) [18,65,40,130,288] 13 := by
  apply FastRouting.sound _ _ [18,65,40,130,288] 13 (by decide) (choices 1) [1,4,8] r7367 c7367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3795
  · exact u3796
  · exact u3797

def b7368 : PairBound 9 := { available := 300, camps := [{ cop := 6, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 19 300 364 428 300), lower := (rows 19 67 44 140 19 32 64 128 256), losses := [] }

theorem u7368 : Upper (D 5) (R 5) [18,65,40,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7368
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7369 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 140 21 298 362 426 298), lower := (rows 19 67 44 140 21 32 64 128 256), losses := [] }

theorem u7369 : Upper (D 5) (R 5) [18,65,40,132,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7369
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7370 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 22 297 361 425 297), lower := (rows 19 67 44 140 22 32 64 128 256), losses := [] }

theorem u7370 : Upper (D 5) (R 5) [18,65,40,132,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7370
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7371 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 140 25 294 358 422 294), lower := (rows 19 67 44 140 25 32 64 128 256), losses := [] }

theorem u7371 : Upper (D 5) (R 5) [18,65,40,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7371
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7372 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 26 293 357 421 293), lower := (rows 19 67 44 140 26 32 64 128 256), losses := [] }

theorem u7372 : Upper (D 5) (R 5) [18,65,40,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7372
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7373 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 355, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 28 291 355 419 291), lower := (rows 19 67 44 140 28 32 64 128 256), losses := [] }

theorem u7373 : Upper (D 5) (R 5) [18,65,40,132,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7373
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7374 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 140 49 302 334 398 270), lower := (rows 19 67 44 140 49 32 64 128 256), losses := [] }

theorem u7374 : Upper (D 5) (R 5) [18,65,40,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7374
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7375 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 50 301 333 397 269), lower := (rows 19 67 44 140 50 32 64 128 256), losses := [] }

theorem u7375 : Upper (D 5) (R 5) [18,65,40,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7375
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7376 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 140 52 299 331 395 267), lower := (rows 19 67 44 140 52 32 64 128 256), losses := [] }

theorem u7376 : Upper (D 5) (R 5) [18,65,40,132,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7376
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7377 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 140 56 295 327 391 263), lower := (rows 19 67 44 140 56 32 64 128 256), losses := [] }

theorem u7377 : Upper (D 5) (R 5) [18,65,40,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7377
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7378 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 172, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 140 273 46 110 174 302), lower := (rows 19 67 44 140 273 32 64 128 256), losses := [] }

theorem u7378 : Upper (D 5) (R 5) [18,65,40,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7378
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7379 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 274 45 109 173 301), lower := (rows 19 67 44 140 274 32 64 128 256), losses := [] }

theorem u7379 : Upper (D 5) (R 5) [18,65,40,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7379
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7379
end Delivery.IrregularNine14.P05
