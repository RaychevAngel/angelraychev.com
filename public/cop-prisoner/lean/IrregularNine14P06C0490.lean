import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0180
import IrregularNine14P06C0181

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r29400 : Route 9 := (fun mask => (mask,id))

def c29400 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29400 : Upper (D 6) (R 6) [6,96,136,48,68] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,68] 13 (by decide) (choices 1) [1,2,256] r29400 c29400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10852
  · exact u10853
  · exact u10854

def r29401 : Route 9 := (fun mask => (mask,id))

def c29401 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29401 : Upper (D 6) (R 6) [6,96,136,48,257] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,257] 13 (by decide) (choices 1) [1,2,4,64] r29401 c29401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10855
  · exact u10856
  · exact u10857
  · exact u10858

def r29402 : Route 9 := (fun mask => (mask,id))

def c29402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29402 : Upper (D 6) (R 6) [6,96,136,48,258] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,258] 13 (by decide) (choices 1) [1,4,64] r29402 c29402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10859
  · exact u10860
  · exact u10861

def r29403 : Route 9 := (fun mask => (mask,id))

def c29403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29403 : Upper (D 6) (R 6) [6,96,136,48,260] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,260] 13 (by decide) (choices 1) [1,2,64] r29403 c29403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10862
  · exact u10863
  · exact u10864

def r29404 : Route 9 := (fun mask => (mask,id))

def c29404 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29404 : Upper (D 6) (R 6) [6,96,136,48,320] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,320] 13 (by decide) (choices 1) [1,2,4] r29404 c29404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10865
  · exact u10866
  · exact u10867

def b29405 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 98 140 265 19 116 116 244 372), lower := (rows 7 98 140 265 19 32 64 128 256), losses := [] }

theorem u29405 : Upper (D 6) (R 6) [6,96,136,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29405
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29406 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 98 140 265 21 114 114 242 370), lower := (rows 7 98 140 265 21 32 64 128 256), losses := [] }

theorem u29406 : Upper (D 6) (R 6) [6,96,136,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29406
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29407 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 98 140 265 22 113 113 241 369), lower := (rows 7 98 140 265 22 32 64 128 256), losses := [] }

theorem u29407 : Upper (D 6) (R 6) [6,96,136,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29407
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29408 : Route 9 := (fun mask => (mask,id))

def c29408 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29408 : Upper (D 6) (R 6) [6,96,136,257,33] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,33] 13 (by decide) (choices 1) [2,4,16,64] r29408 c29408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10868
  · exact u10869
  · exact u10870
  · exact u10871

def b29409 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 98 140 265 50 117 85 213 341), lower := (rows 7 98 140 265 50 32 64 128 256), losses := [] }

theorem u29409 : Upper (D 6) (R 6) [6,96,136,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29409
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29410 : Route 9 := (fun mask => (mask,id))

def c29410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29410 : Upper (D 6) (R 6) [6,96,136,257,36] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,36] 13 (by decide) (choices 1) [1,2,16,64] r29410 c29410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10872
  · exact u10873
  · exact u10874
  · exact u10875

def b29411 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 98 140 265 112 55 87 151 279), lower := (rows 7 98 140 265 112 32 64 128 256), losses := [] }

theorem u29411 : Upper (D 6) (R 6) [6,96,136,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29411
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29412 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 98 140 266 21 113 113 241 369), lower := (rows 7 98 140 266 21 32 64 128 256), losses := [] }

theorem u29412 : Upper (D 6) (R 6) [6,96,136,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29412
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29413 : Route 9 := (fun mask => (mask,id))

def c29413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29413 : Upper (D 6) (R 6) [6,96,136,258,33] 13 := by
  apply FastRouting.sound _ _ [6,96,136,258,33] 13 (by decide) (choices 1) [1,4,16,64] r29413 c29413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10876
  · exact u10877
  · exact u10878
  · exact u10879

def r29414 : Route 9 := (fun mask => (mask,id))

def c29414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29414 : Upper (D 6) (R 6) [6,96,136,258,36] 13 := by
  apply FastRouting.sound _ _ [6,96,136,258,36] 13 (by decide) (choices 1) [1,16,64] r29414 c29414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10880
  · exact u10881
  · exact u10882

def b29415 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 98 140 266 112 53 85 149 277), lower := (rows 7 98 140 266 112 32 64 128 256), losses := [] }

theorem u29415 : Upper (D 6) (R 6) [6,96,136,258,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29415
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29416 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 114, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 7 98 140 268 19 113 113 241 369), lower := (rows 7 98 140 268 19 32 64 128 256), losses := [] }

theorem u29416 : Upper (D 6) (R 6) [6,96,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29416
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29417 : Route 9 := (fun mask => (mask,id))

def c29417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29417 : Upper (D 6) (R 6) [6,96,136,260,33] 13 := by
  apply FastRouting.sound _ _ [6,96,136,260,33] 13 (by decide) (choices 1) [1,2,16,64] r29417 c29417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10883
  · exact u10884
  · exact u10885
  · exact u10886

def b29418 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 98 140 268 50 113 81 209 337), lower := (rows 7 98 140 268 50 32 64 128 256), losses := [] }

theorem u29418 : Upper (D 6) (R 6) [6,96,136,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29418
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29419 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 114, targets := 4 },{ cop := 1, region := 16, targets := 1 }], pairs := [(1,2),(4,0),(4,2)], upper := (rows 7 98 140 268 112 51 83 147 275), lower := (rows 7 98 140 268 112 32 64 128 256), losses := [] }

theorem u29419 : Upper (D 6) (R 6) [6,96,136,260,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29419
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29420 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 98 140 280 19 101 101 229 357), lower := (rows 7 98 140 280 19 32 64 128 256), losses := [] }

theorem u29420 : Upper (D 6) (R 6) [6,96,136,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29420
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29421 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 98 140 280 21 99 99 227 355), lower := (rows 7 98 140 280 21 32 64 128 256), losses := [] }

theorem u29421 : Upper (D 6) (R 6) [6,96,136,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29421
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29422 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 98 140 280 22 97 97 225 353), lower := (rows 7 98 140 280 22 32 64 128 256), losses := [] }

theorem u29422 : Upper (D 6) (R 6) [6,96,136,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29422
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29423 : Route 9 := (fun mask => (mask,id))

def c29423 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29423 : Upper (D 6) (R 6) [6,96,136,272,33] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272,33] 13 (by decide) (choices 1) [1,2,4,64] r29423 c29423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10887
  · exact u10888
  · exact u10889
  · exact u10890

def b29424 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 98 140 280 50 101 69 197 325), lower := (rows 7 98 140 280 50 32 64 128 256), losses := [] }

theorem u29424 : Upper (D 6) (R 6) [6,96,136,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29424
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29425 : Route 9 := (fun mask => (mask,id))

def c29425 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29425 : Upper (D 6) (R 6) [6,96,136,272,36] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272,36] 13 (by decide) (choices 1) [1,2,64] r29425 c29425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10891
  · exact u10892
  · exact u10893

def b29426 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 98 140 280 112 39 71 135 263), lower := (rows 7 98 140 280 112 32 64 128 256), losses := [] }

theorem u29426 : Upper (D 6) (R 6) [6,96,136,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29426
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29427 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 98 140 296 19 117 85 213 341), lower := (rows 7 98 140 296 19 32 64 128 256), losses := [] }

theorem u29427 : Upper (D 6) (R 6) [6,96,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29427
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29428 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 98 140 296 21 115 83 211 339), lower := (rows 7 98 140 296 21 32 64 128 256), losses := [] }

theorem u29428 : Upper (D 6) (R 6) [6,96,136,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29428
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29429 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 98 140 296 22 113 81 209 337), lower := (rows 7 98 140 296 22 32 64 128 256), losses := [] }

theorem u29429 : Upper (D 6) (R 6) [6,96,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29429
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29430 : Route 9 := (fun mask => (mask,id))

def c29430 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29430 : Upper (D 6) (R 6) [6,96,136,288,65] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,65] 13 (by decide) (choices 1) [1,2,4,16] r29430 c29430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10894
  · exact u10895
  · exact u10896
  · exact u10897

def b29431 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 7 98 140 296 82 53 85 149 277), lower := (rows 7 98 140 296 82 32 64 128 256), losses := [] }

theorem u29431 : Upper (D 6) (R 6) [6,96,136,288,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29431
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29432 : Route 9 := (fun mask => (mask,id))

def c29432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29432 : Upper (D 6) (R 6) [6,96,136,288,68] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,68] 13 (by decide) (choices 1) [1,2,16] r29432 c29432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10898
  · exact u10899
  · exact u10900

def b29433 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 98 164 11 25 372 340 468 340), lower := (rows 7 98 164 11 25 32 64 128 256), losses := [] }

theorem u29433 : Upper (D 6) (R 6) [6,96,160,3,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29433
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29434 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 24, targets := 32 },{ cop := 0, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 164 11 28 369 337 465 337), lower := (rows 7 98 164 11 28 32 64 128 256), losses := [] }

theorem u29434 : Upper (D 6) (R 6) [6,96,160,3,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29434
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29435 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 164 11 81 316 348 412 284), lower := (rows 7 98 164 11 81 32 64 128 256), losses := [] }

theorem u29435 : Upper (D 6) (R 6) [6,96,160,3,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29435
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29436 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 164 11 84 313 345 409 281), lower := (rows 7 98 164 11 84 32 64 128 256), losses := [] }

theorem u29436 : Upper (D 6) (R 6) [6,96,160,3,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29436
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29437 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 164 11 88 309 341 405 277), lower := (rows 7 98 164 11 88 32 64 128 256), losses := [] }

theorem u29437 : Upper (D 6) (R 6) [6,96,160,3,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29437
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29438 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 164 11 273 124 92 220 348), lower := (rows 7 98 164 11 273 32 64 128 256), losses := [] }

theorem u29438 : Upper (D 6) (R 6) [6,96,160,3,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29438
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29439 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 164 11 276 121 89 217 345), lower := (rows 7 98 164 11 276 32 64 128 256), losses := [] }

theorem u29439 : Upper (D 6) (R 6) [6,96,160,3,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29439
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29440 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 164 11 280 117 85 213 341), lower := (rows 7 98 164 11 280 32 64 128 256), losses := [] }

theorem u29440 : Upper (D 6) (R 6) [6,96,160,3,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29440
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29441 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 164 11 336 61 93 157 285), lower := (rows 7 98 164 11 336 32 64 128 256), losses := [] }

theorem u29441 : Upper (D 6) (R 6) [6,96,160,3,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29441
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29442 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 98 164 13 25 370 338 466 338), lower := (rows 7 98 164 13 25 32 64 128 256), losses := [] }

theorem u29442 : Upper (D 6) (R 6) [6,96,160,5,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29442
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29443 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 24, targets := 32 },{ cop := 0, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 164 13 26 369 337 465 337), lower := (rows 7 98 164 13 26 32 64 128 256), losses := [] }

theorem u29443 : Upper (D 6) (R 6) [6,96,160,5,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29443
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29444 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 164 13 81 314 346 410 282), lower := (rows 7 98 164 13 81 32 64 128 256), losses := [] }

theorem u29444 : Upper (D 6) (R 6) [6,96,160,5,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29444
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29445 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 164 13 88 307 339 403 275), lower := (rows 7 98 164 13 88 32 64 128 256), losses := [] }

theorem u29445 : Upper (D 6) (R 6) [6,96,160,5,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29445
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29446 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 164 13 273 122 90 218 346), lower := (rows 7 98 164 13 273 32 64 128 256), losses := [] }

theorem u29446 : Upper (D 6) (R 6) [6,96,160,5,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29446
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29447 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 164 13 274 121 89 217 345), lower := (rows 7 98 164 13 274 32 64 128 256), losses := [] }

theorem u29447 : Upper (D 6) (R 6) [6,96,160,5,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29447
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29448 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 164 13 280 115 83 211 339), lower := (rows 7 98 164 13 280 32 64 128 256), losses := [] }

theorem u29448 : Upper (D 6) (R 6) [6,96,160,5,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29448
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29449 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 164 13 336 59 91 155 283), lower := (rows 7 98 164 13 336 32 64 128 256), losses := [] }

theorem u29449 : Upper (D 6) (R 6) [6,96,160,5,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29449
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29450 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 24, targets := 32 },{ cop := 0, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 164 14 25 369 337 465 337), lower := (rows 7 98 164 14 25 32 64 128 256), losses := [] }

theorem u29450 : Upper (D 6) (R 6) [6,96,160,6,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29450
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29451 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 98 164 14 81 313 345 409 281), lower := (rows 7 98 164 14 81 32 64 128 256), losses := [] }

theorem u29451 : Upper (D 6) (R 6) [6,96,160,6,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29451
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29452 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 98 164 14 88 305 337 401 273), lower := (rows 7 98 164 14 88 32 64 128 256), losses := [] }

theorem u29452 : Upper (D 6) (R 6) [6,96,160,6,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29452
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29453 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 98 164 14 273 121 89 217 345), lower := (rows 7 98 164 14 273 32 64 128 256), losses := [] }

theorem u29453 : Upper (D 6) (R 6) [6,96,160,6,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29453
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29454 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 98 164 14 280 113 81 209 337), lower := (rows 7 98 164 14 280 32 64 128 256), losses := [] }

theorem u29454 : Upper (D 6) (R 6) [6,96,160,6,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29454
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29455 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 98 164 14 336 57 89 153 281), lower := (rows 7 98 164 14 336 32 64 128 256), losses := [] }

theorem u29455 : Upper (D 6) (R 6) [6,96,160,6,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29455
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29456 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 98 164 25 25 358 326 454 326), lower := (rows 7 98 164 25 25 32 64 128 256), losses := [] }

theorem u29456 : Upper (D 6) (R 6) [6,96,160,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29456
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29457 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 98 164 25 26 357 325 453 325), lower := (rows 7 98 164 25 26 32 64 128 256), losses := [] }

theorem u29457 : Upper (D 6) (R 6) [6,96,160,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29457
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29458 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 98 164 25 28 355 323 451 323), lower := (rows 7 98 164 25 28 32 64 128 256), losses := [] }

theorem u29458 : Upper (D 6) (R 6) [6,96,160,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29458
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29459 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 98 164 25 81 302 334 398 270), lower := (rows 7 98 164 25 81 32 64 128 256), losses := [] }

theorem u29459 : Upper (D 6) (R 6) [6,96,160,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29459
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29459
end Delivery.IrregularNine14.P06
