import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0179
import IrregularNine14P06C0180

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29340 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 133 42 88 309 341 405 277), lower := (rows 7 98 133 42 88 32 64 128 256), losses := [] }

theorem u29340 : Upper (D 6) (R 6) [6,96,129,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29340
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29341 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 133 42 273 124 92 220 348), lower := (rows 7 98 133 42 273 32 64 128 256), losses := [] }

theorem u29341 : Upper (D 6) (R 6) [6,96,129,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29341
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29342 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 133 42 276 121 89 217 345), lower := (rows 7 98 133 42 276 32 64 128 256), losses := [] }

theorem u29342 : Upper (D 6) (R 6) [6,96,129,34,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29342
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29343 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 133 42 280 117 85 213 341), lower := (rows 7 98 133 42 280 32 64 128 256), losses := [] }

theorem u29343 : Upper (D 6) (R 6) [6,96,129,34,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29343
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29344 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 98 133 42 336 61 93 157 285), lower := (rows 7 98 133 42 336 32 64 128 256), losses := [] }

theorem u29344 : Upper (D 6) (R 6) [6,96,129,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29344
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29345 : Route 9 := (fun mask => (mask,id))

def c29345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29345 : Upper (D 6) (R 6) [6,96,129,36,72] 13 := by
  apply FastRouting.sound _ _ [6,96,129,36,72] 13 (by decide) (choices 1) [1,2,16,256] r29345 c29345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10761
  · exact u10762
  · exact u10763
  · exact u10764

def r29346 : Route 9 := (fun mask => (mask,id))

def c29346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29346 : Upper (D 6) (R 6) [6,96,129,36,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,36,257] 13 (by decide) (choices 1) [2,8,16,64] r29346 c29346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10765
  · exact u10766
  · exact u10767
  · exact u10768

def r29347 : Route 9 := (fun mask => (mask,id))

def c29347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29347 : Upper (D 6) (R 6) [6,96,129,36,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,36,258] 13 (by decide) (choices 1) [1,8,16,64] r29347 c29347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10769
  · exact u10770
  · exact u10771
  · exact u10772

def r29348 : Route 9 := (fun mask => (mask,id))

def c29348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29348 : Upper (D 6) (R 6) [6,96,129,36,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,36,264] 13 (by decide) (choices 1) [1,2,16,64] r29348 c29348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10773
  · exact u10774
  · exact u10775
  · exact u10776

def r29349 : Route 9 := (fun mask => (mask,id))

def c29349 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29349 : Upper (D 6) (R 6) [6,96,129,36,320] 13 := by
  apply FastRouting.sound _ _ [6,96,129,36,320] 13 (by decide) (choices 1) [1,2,8,16] r29349 c29349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10777
  · exact u10778
  · exact u10779
  · exact u10780

def b29350 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 133 56 88 295 327 391 263), lower := (rows 7 98 133 56 88 32 64 128 256), losses := [] }

theorem u29350 : Upper (D 6) (R 6) [6,96,129,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29350
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29351 : Route 9 := (fun mask => (mask,id))

def c29351 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29351 : Upper (D 6) (R 6) [6,96,129,48,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,257] 13 (by decide) (choices 1) [2,4,8,64] r29351 c29351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10781
  · exact u10782
  · exact u10783
  · exact u10784

def r29352 : Route 9 := (fun mask => (mask,id))

def c29352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29352 : Upper (D 6) (R 6) [6,96,129,48,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,258] 13 (by decide) (choices 1) [1,4,8,64] r29352 c29352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10785
  · exact u10786
  · exact u10787
  · exact u10788

def r29353 : Route 9 := (fun mask => (mask,id))

def c29353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29353 : Upper (D 6) (R 6) [6,96,129,48,260] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,260] 13 (by decide) (choices 1) [1,2,8,64] r29353 c29353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10789
  · exact u10790
  · exact u10791
  · exact u10792

def r29354 : Route 9 := (fun mask => (mask,id))

def c29354 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29354 : Upper (D 6) (R 6) [6,96,129,48,264] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,264] 13 (by decide) (choices 1) [1,2,4,64] r29354 c29354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10793
  · exact u10794
  · exact u10795
  · exact u10796

def r29355 : Route 9 := (fun mask => (mask,id))

def c29355 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29355 : Upper (D 6) (R 6) [6,96,129,48,320] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,320] 13 (by decide) (choices 1) [1,2,4,8] r29355 c29355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10797
  · exact u10798
  · exact u10799
  · exact u10800

def b29356 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 7 98 133 104 273 62 94 158 286), lower := (rows 7 98 133 104 273 32 64 128 256), losses := [] }

theorem u29356 : Upper (D 6) (R 6) [6,96,129,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29356
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29357 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 7 98 133 104 274 61 93 157 285), lower := (rows 7 98 133 104 274 32 64 128 256), losses := [] }

theorem u29357 : Upper (D 6) (R 6) [6,96,129,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29357
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29358 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 7 98 133 104 276 59 91 155 283), lower := (rows 7 98 133 104 276 32 64 128 256), losses := [] }

theorem u29358 : Upper (D 6) (R 6) [6,96,129,96,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29358
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29359 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 7 98 133 104 280 55 87 151 279), lower := (rows 7 98 133 104 280 32 64 128 256), losses := [] }

theorem u29359 : Upper (D 6) (R 6) [6,96,129,96,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29359
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29360 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 140 25 19 356 356 484 356), lower := (rows 7 98 140 25 19 32 64 128 256), losses := [] }

theorem u29360 : Upper (D 6) (R 6) [6,96,136,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29360
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29361 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 140 25 21 354 354 482 354), lower := (rows 7 98 140 25 21 32 64 128 256), losses := [] }

theorem u29361 : Upper (D 6) (R 6) [6,96,136,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29361
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29362 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 140 25 22 353 353 481 353), lower := (rows 7 98 140 25 22 32 64 128 256), losses := [] }

theorem u29362 : Upper (D 6) (R 6) [6,96,136,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29362
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29363 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 98 140 25 49 358 326 454 326), lower := (rows 7 98 140 25 49 32 64 128 256), losses := [] }

theorem u29363 : Upper (D 6) (R 6) [6,96,136,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29363
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29364 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 98 140 25 50 357 325 453 325), lower := (rows 7 98 140 25 50 32 64 128 256), losses := [] }

theorem u29364 : Upper (D 6) (R 6) [6,96,136,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29364
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29365 : Route 9 := (fun mask => (mask,id))

def c29365 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29365 : Upper (D 6) (R 6) [6,96,136,17,36] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,36] 13 (by decide) (choices 1) [1,2,64,256] r29365 c29365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10801
  · exact u10802
  · exact u10803
  · exact u10804

def b29366 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 98 140 25 112 295 327 391 263), lower := (rows 7 98 140 25 112 32 64 128 256), losses := [] }

theorem u29366 : Upper (D 6) (R 6) [6,96,136,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29366
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29367 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 98 140 25 273 102 102 230 358), lower := (rows 7 98 140 25 273 32 64 128 256), losses := [] }

theorem u29367 : Upper (D 6) (R 6) [6,96,136,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29367
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29368 : Route 9 := (fun mask => (mask,id))

def c29368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29368 : Upper (D 6) (R 6) [6,96,136,17,258] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,258] 13 (by decide) (choices 1) [1,4,64] r29368 c29368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10805
  · exact u10806
  · exact u10807

def r29369 : Route 9 := (fun mask => (mask,id))

def c29369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29369 : Upper (D 6) (R 6) [6,96,136,17,260] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,260] 13 (by decide) (choices 1) [1,2,64] r29369 c29369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10808
  · exact u10809
  · exact u10810

def r29370 : Route 9 := (fun mask => (mask,id))

def c29370 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29370 : Upper (D 6) (R 6) [6,96,136,17,288] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,288] 13 (by decide) (choices 1) [1,2,4,64] r29370 c29370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10811
  · exact u10812
  · exact u10813
  · exact u10814

def b29371 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 140 26 21 353 353 481 353), lower := (rows 7 98 140 26 21 32 64 128 256), losses := [] }

theorem u29371 : Upper (D 6) (R 6) [6,96,136,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29371
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29372 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 0, region := 368, targets := 2 }], pairs := [(0,5),(2,5),(4,1)], upper := (rows 7 98 140 26 49 357 325 453 325), lower := (rows 7 98 140 26 49 32 64 128 256), losses := [] }

theorem u29372 : Upper (D 6) (R 6) [6,96,136,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29372
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29373 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 0, region := 368, targets := 2 }], pairs := [(0,5),(2,5),(4,1)], upper := (rows 7 98 140 26 52 353 321 449 321), lower := (rows 7 98 140 26 52 32 64 128 256), losses := [] }

theorem u29373 : Upper (D 6) (R 6) [6,96,136,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29373
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29374 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 140 26 112 293 325 389 261), lower := (rows 7 98 140 26 112 32 64 128 256), losses := [] }

theorem u29374 : Upper (D 6) (R 6) [6,96,136,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29374
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29375 : Route 9 := (fun mask => (mask,id))

def c29375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29375 : Upper (D 6) (R 6) [6,96,136,18,257] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,257] 13 (by decide) (choices 1) [1,4,64] r29375 c29375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10815
  · exact u10816
  · exact u10817

def r29376 : Route 9 := (fun mask => (mask,id))

def c29376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29376 : Upper (D 6) (R 6) [6,96,136,18,260] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,260] 13 (by decide) (choices 1) [1,64] r29376 c29376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10818
  · exact u10819

def b29377 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 197, targets := 32 },{ cop := 0, region := 368, targets := 2 }], pairs := [(0,5),(2,5),(4,1)], upper := (rows 7 98 140 26 304 101 69 197 325), lower := (rows 7 98 140 26 304 32 64 128 256), losses := [] }

theorem u29377 : Upper (D 6) (R 6) [6,96,136,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29377
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29378 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 140 28 19 353 353 481 353), lower := (rows 7 98 140 28 19 32 64 128 256), losses := [] }

theorem u29378 : Upper (D 6) (R 6) [6,96,136,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29378
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29379 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(2,5),(4,2)], upper := (rows 7 98 140 28 49 355 323 451 323), lower := (rows 7 98 140 28 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 65 129 257), good := (rows 455 66 140 28 477 0 64 128 256) }] }

theorem u29379 : Upper (D 6) (R 6) [6,96,136,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29379
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29380 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 98 140 28 50 353 321 449 321), lower := (rows 7 98 140 28 50 32 64 128 256), losses := [] }

theorem u29380 : Upper (D 6) (R 6) [6,96,136,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29380
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29381 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 16, targets := 1 }], pairs := [(1,2),(4,0),(4,2)], upper := (rows 7 98 140 28 112 291 323 387 259), lower := (rows 7 98 140 28 112 32 64 128 256), losses := [] }

theorem u29381 : Upper (D 6) (R 6) [6,96,136,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29381
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29382 : Route 9 := (fun mask => (mask,id))

def c29382 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29382 : Upper (D 6) (R 6) [6,96,136,20,257] 13 := by
  apply FastRouting.sound _ _ [6,96,136,20,257] 13 (by decide) (choices 1) [1,2,64] r29382 c29382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10820
  · exact u10821
  · exact u10822

def r29383 : Route 9 := (fun mask => (mask,id))

def c29383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29383 : Upper (D 6) (R 6) [6,96,136,20,258] 13 := by
  apply FastRouting.sound _ _ [6,96,136,20,258] 13 (by decide) (choices 1) [1,64] r29383 c29383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10823
  · exact u10824

def r29384 : Route 9 := (fun mask => (mask,id))

def c29384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29384 : Upper (D 6) (R 6) [6,96,136,20,288] 13 := by
  apply FastRouting.sound _ _ [6,96,136,20,288] 13 (by decide) (choices 1) [1,2,64] r29384 c29384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10825
  · exact u10826
  · exact u10827

def b29385 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 98 140 41 19 372 340 468 340), lower := (rows 7 98 140 41 19 32 64 128 256), losses := [] }

theorem u29385 : Upper (D 6) (R 6) [6,96,136,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29385
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29386 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 98 140 41 21 370 338 466 338), lower := (rows 7 98 140 41 21 32 64 128 256), losses := [] }

theorem u29386 : Upper (D 6) (R 6) [6,96,136,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29386
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29387 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 98 140 41 22 369 337 465 337), lower := (rows 7 98 140 41 22 32 64 128 256), losses := [] }

theorem u29387 : Upper (D 6) (R 6) [6,96,136,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29387
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29388 : Route 9 := (fun mask => (mask,id))

def c29388 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29388 : Upper (D 6) (R 6) [6,96,136,33,65] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,65] 13 (by decide) (choices 1) [2,4,16,256] r29388 c29388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10828
  · exact u10829
  · exact u10830
  · exact u10831

def b29389 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 7 98 140 41 82 309 341 405 277), lower := (rows 7 98 140 41 82 32 64 128 256), losses := [] }

theorem u29389 : Upper (D 6) (R 6) [6,96,136,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29389
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29390 : Route 9 := (fun mask => (mask,id))

def c29390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29390 : Upper (D 6) (R 6) [6,96,136,33,68] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,68] 13 (by decide) (choices 1) [1,2,16,256] r29390 c29390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10832
  · exact u10833
  · exact u10834
  · exact u10835

def r29391 : Route 9 := (fun mask => (mask,id))

def c29391 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29391 : Upper (D 6) (R 6) [6,96,136,33,257] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,257] 13 (by decide) (choices 1) [2,4,16,64] r29391 c29391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10836
  · exact u10837
  · exact u10838
  · exact u10839

def r29392 : Route 9 := (fun mask => (mask,id))

def c29392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29392 : Upper (D 6) (R 6) [6,96,136,33,258] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,258] 13 (by decide) (choices 1) [1,4,16,64] r29392 c29392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10840
  · exact u10841
  · exact u10842
  · exact u10843

def r29393 : Route 9 := (fun mask => (mask,id))

def c29393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29393 : Upper (D 6) (R 6) [6,96,136,33,260] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,260] 13 (by decide) (choices 1) [1,2,16,64] r29393 c29393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10844
  · exact u10845
  · exact u10846
  · exact u10847

def r29394 : Route 9 := (fun mask => (mask,id))

def c29394 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29394 : Upper (D 6) (R 6) [6,96,136,33,320] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,320] 13 (by decide) (choices 1) [1,2,4,16] r29394 c29394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10848
  · exact u10849
  · exact u10850
  · exact u10851

def b29395 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 98 140 56 19 357 325 453 325), lower := (rows 7 98 140 56 19 32 64 128 256), losses := [] }

theorem u29395 : Upper (D 6) (R 6) [6,96,136,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29395
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29396 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 98 140 56 21 355 323 451 323), lower := (rows 7 98 140 56 21 32 64 128 256), losses := [] }

theorem u29396 : Upper (D 6) (R 6) [6,96,136,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29396
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29397 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 354, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(4,0),(4,5)], upper := (rows 7 98 140 56 22 353 321 449 321), lower := (rows 7 98 140 56 22 32 64 128 256), losses := [] }

theorem u29397 : Upper (D 6) (R 6) [6,96,136,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29397
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29398 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(2,6),(3,6),(4,5)], upper := (rows 7 98 140 56 81 295 327 391 263), lower := (rows 7 98 140 56 81 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 33 0 129 257), good := (rows 423 34 140 60 445 32 0 128 256) }] }

theorem u29398 : Upper (D 6) (R 6) [6,96,136,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29398
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29399 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 98 140 56 82 293 325 389 261), lower := (rows 7 98 140 56 82 32 64 128 256), losses := [] }

theorem u29399 : Upper (D 6) (R 6) [6,96,136,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29399
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29399
end Delivery.IrregularNine14.P06
