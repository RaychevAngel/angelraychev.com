import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0181
import IrregularNine14P06C0182
import IrregularNine14P06C0183

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29460 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 7 98 164 25 82 301 333 397 269), lower := (rows 7 98 164 25 82 32 64 128 256), losses := [] }

theorem u29460 : Upper (D 6) (R 6) [6,96,160,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29460
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29461 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 354, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 98 164 25 84 299 331 395 267), lower := (rows 7 98 164 25 84 32 64 128 256), losses := [] }

theorem u29461 : Upper (D 6) (R 6) [6,96,160,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29461
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29462 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 25 88 295 327 391 263), lower := (rows 7 98 164 25 88 32 64 128 256), losses := [] }

theorem u29462 : Upper (D 6) (R 6) [6,96,160,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29462
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29463 : PairBound 9 := { available := 78, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 98 164 25 273 110 78 206 334), lower := (rows 7 98 164 25 273 32 64 128 256), losses := [] }

theorem u29463 : Upper (D 6) (R 6) [6,96,160,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29463
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29464 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 98 164 25 274 109 77 205 333), lower := (rows 7 98 164 25 274 32 64 128 256), losses := [] }

theorem u29464 : Upper (D 6) (R 6) [6,96,160,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29464
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29465 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 98 164 25 276 107 75 203 331), lower := (rows 7 98 164 25 276 32 64 128 256), losses := [] }

theorem u29465 : Upper (D 6) (R 6) [6,96,160,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29465
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29466 : Route 9 := (fun mask => (mask,id))

def c29466 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29466 : Upper (D 6) (R 6) [6,96,160,17,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,264] 13 (by decide) (choices 1) [1,2,4,64] r29466 c29466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10901
  · exact u10902
  · exact u10903
  · exact u10904

def r29467 : Route 9 := (fun mask => (mask,id))

def c29467 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29467 : Upper (D 6) (R 6) [6,96,160,17,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,320] 13 (by decide) (choices 1) [1,2,4,8] r29467 c29467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10905
  · exact u10906
  · exact u10907
  · exact u10908

def b29468 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 24, targets := 1 },{ cop := 0, region := 24, targets := 32 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 7 98 164 26 28 353 321 449 321), lower := (rows 7 98 164 26 28 32 64 128 256), losses := [] }

theorem u29468 : Upper (D 6) (R 6) [6,96,160,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29468
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29469 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 26 81 301 333 397 269), lower := (rows 7 98 164 26 81 32 64 128 256), losses := [] }

theorem u29469 : Upper (D 6) (R 6) [6,96,160,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29469
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29470 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 26 84 297 329 393 265), lower := (rows 7 98 164 26 84 32 64 128 256), losses := [] }

theorem u29470 : Upper (D 6) (R 6) [6,96,160,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29470
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29471 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 7 98 164 26 88 293 325 389 261), lower := (rows 7 98 164 26 88 32 64 128 256), losses := [] }

theorem u29471 : Upper (D 6) (R 6) [6,96,160,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29471
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29472 : Route 9 := (fun mask => (mask,id))

def c29472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29472 : Upper (D 6) (R 6) [6,96,160,18,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,257] 13 (by decide) (choices 1) [1,4,8,64] r29472 c29472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10909
  · exact u10910
  · exact u10911
  · exact u10912

def r29473 : Route 9 := (fun mask => (mask,id))

def c29473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29473 : Upper (D 6) (R 6) [6,96,160,18,260] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,260] 13 (by decide) (choices 1) [1,8,64] r29473 c29473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10913
  · exact u10914
  · exact u10915

def b29474 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 98 164 26 280 101 69 197 325), lower := (rows 7 98 164 26 280 32 64 128 256), losses := [] }

theorem u29474 : Upper (D 6) (R 6) [6,96,160,18,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29474
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29475 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 26 336 45 77 141 269), lower := (rows 7 98 164 26 336 32 64 128 256), losses := [] }

theorem u29475 : Upper (D 6) (R 6) [6,96,160,18,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29475
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29476 : Route 9 := (fun mask => (mask,id))

def c29476 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29476 : Upper (D 6) (R 6) [6,96,160,20,65] 13 := by
  apply FastRouting.sound _ _ [6,96,160,20,65] 13 (by decide) (choices 1) [1,2,8,256] r29476 c29476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10916
  · exact u10917
  · exact u10918
  · exact u10919

def b29477 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 7 98 164 28 82 297 329 393 265), lower := (rows 7 98 164 28 82 32 64 128 256), losses := [] }

theorem u29477 : Upper (D 6) (R 6) [6,96,160,20,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29477
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29478 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 28 88 291 323 387 259), lower := (rows 7 98 164 28 88 32 64 128 256), losses := [] }

theorem u29478 : Upper (D 6) (R 6) [6,96,160,20,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29478
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29479 : Route 9 := (fun mask => (mask,id))

def c29479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29479 : Upper (D 6) (R 6) [6,96,160,20,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,20,257] 13 (by decide) (choices 1) [1,2,8,64] r29479 c29479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10920
  · exact u10921
  · exact u10922
  · exact u10923

def r29480 : Route 9 := (fun mask => (mask,id))

def c29480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29480 : Upper (D 6) (R 6) [6,96,160,20,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,20,258] 13 (by decide) (choices 1) [1,8,64] r29480 c29480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10924
  · exact u10925
  · exact u10926

def b29481 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 98 164 28 280 99 67 195 323), lower := (rows 7 98 164 28 280 32 64 128 256), losses := [] }

theorem u29481 : Upper (D 6) (R 6) [6,96,160,20,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29481
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29482 : Route 9 := (fun mask => (mask,id))

def c29482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29482 : Upper (D 6) (R 6) [6,96,160,20,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,20,320] 13 (by decide) (choices 1) [1,2,8] r29482 c29482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10927
  · exact u10928
  · exact u10929

def r29483 : Route 9 := (fun mask => (mask,id))

def c29483 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29483 : Upper (D 6) (R 6) [6,96,160,65,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,257] 13 (by decide) (choices 1) [2,4,8,16] r29483 c29483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10930
  · exact u10931
  · exact u10932
  · exact u10933

def r29484 : Route 9 := (fun mask => (mask,id))

def c29484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29484 : Upper (D 6) (R 6) [6,96,160,65,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,258] 13 (by decide) (choices 1) [1,4,8,16] r29484 c29484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10934
  · exact u10935
  · exact u10936
  · exact u10937

def r29485 : Route 9 := (fun mask => (mask,id))

def c29485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29485 : Upper (D 6) (R 6) [6,96,160,65,260] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,260] 13 (by decide) (choices 1) [1,2,8,16] r29485 c29485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10938
  · exact u10939
  · exact u10940
  · exact u10941

def r29486 : Route 9 := (fun mask => (mask,id))

def c29486 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29486 : Upper (D 6) (R 6) [6,96,160,65,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,264] 13 (by decide) (choices 1) [1,2,4,16] r29486 c29486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10942
  · exact u10943
  · exact u10944
  · exact u10945

def b29487 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 7 98 164 74 273 61 93 157 285), lower := (rows 7 98 164 74 273 32 64 128 256), losses := [] }

theorem u29487 : Upper (D 6) (R 6) [6,96,160,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29487
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29488 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 7 98 164 74 276 57 89 153 281), lower := (rows 7 98 164 74 276 32 64 128 256), losses := [] }

theorem u29488 : Upper (D 6) (R 6) [6,96,160,66,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29488
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29489 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 7 98 164 74 280 53 85 149 277), lower := (rows 7 98 164 74 280 32 64 128 256), losses := [] }

theorem u29489 : Upper (D 6) (R 6) [6,96,160,66,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29489
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29490 : Route 9 := (fun mask => (mask,id))

def c29490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29490 : Upper (D 6) (R 6) [6,96,160,68,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,68,257] 13 (by decide) (choices 1) [1,2,8,16] r29490 c29490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10946
  · exact u10947
  · exact u10948
  · exact u10949

def r29491 : Route 9 := (fun mask => (mask,id))

def c29491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29491 : Upper (D 6) (R 6) [6,96,160,68,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,68,258] 13 (by decide) (choices 1) [1,8,16] r29491 c29491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10950
  · exact u10951
  · exact u10952

def r29492 : Route 9 := (fun mask => (mask,id))

def c29492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29492 : Upper (D 6) (R 6) [6,96,160,68,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,68,264] 13 (by decide) (choices 1) [1,2,16] r29492 c29492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10953
  · exact u10954
  · exact u10955

def r29493 : Route 9 := (fun mask => (mask,id))

def c29493 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29493 : Upper (D 6) (R 6) [6,96,160,80,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,257] 13 (by decide) (choices 1) [1,2,4,8] r29493 c29493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10956
  · exact u10957
  · exact u10958
  · exact u10959

def r29494 : Route 9 := (fun mask => (mask,id))

def c29494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29494 : Upper (D 6) (R 6) [6,96,160,80,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,258] 13 (by decide) (choices 1) [1,4,8] r29494 c29494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10960
  · exact u10961
  · exact u10962

def r29495 : Route 9 := (fun mask => (mask,id))

def c29495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29495 : Upper (D 6) (R 6) [6,96,160,80,260] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,260] 13 (by decide) (choices 1) [1,2,8] r29495 c29495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10963
  · exact u10964
  · exact u10965

def b29496 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 88 280 39 71 135 263), lower := (rows 7 98 164 88 280 32 64 128 256), losses := [] }

theorem u29496 : Upper (D 6) (R 6) [6,96,160,80,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29496
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29497 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 388 11 25 116 116 244 372), lower := (rows 7 98 388 11 25 32 64 128 256), losses := [] }

theorem u29497 : Upper (D 6) (R 6) [6,96,384,3,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29497
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29498 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 388 11 28 113 113 241 369), lower := (rows 7 98 388 11 28 32 64 128 256), losses := [] }

theorem u29498 : Upper (D 6) (R 6) [6,96,384,3,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29498
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29499 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 388 11 49 124 92 220 348), lower := (rows 7 98 388 11 49 32 64 128 256), losses := [] }

theorem u29499 : Upper (D 6) (R 6) [6,96,384,3,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29499
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29500 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 388 11 52 121 89 217 345), lower := (rows 7 98 388 11 52 32 64 128 256), losses := [] }

theorem u29500 : Upper (D 6) (R 6) [6,96,384,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29500
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29501 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 388 11 56 117 85 213 341), lower := (rows 7 98 388 11 56 32 64 128 256), losses := [] }

theorem u29501 : Upper (D 6) (R 6) [6,96,384,3,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29501
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29502 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 388 13 25 114 114 242 370), lower := (rows 7 98 388 13 25 32 64 128 256), losses := [] }

theorem u29502 : Upper (D 6) (R 6) [6,96,384,5,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29502
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29503 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 388 13 26 113 113 241 369), lower := (rows 7 98 388 13 26 32 64 128 256), losses := [] }

theorem u29503 : Upper (D 6) (R 6) [6,96,384,5,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29503
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29504 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 388 13 49 122 90 218 346), lower := (rows 7 98 388 13 49 32 64 128 256), losses := [] }

theorem u29504 : Upper (D 6) (R 6) [6,96,384,5,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29504
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29505 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 388 13 56 115 83 211 339), lower := (rows 7 98 388 13 56 32 64 128 256), losses := [] }

theorem u29505 : Upper (D 6) (R 6) [6,96,384,5,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29505
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29506 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 388 14 25 113 113 241 369), lower := (rows 7 98 388 14 25 32 64 128 256), losses := [] }

theorem u29506 : Upper (D 6) (R 6) [6,96,384,6,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29506
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29507 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 98 388 14 49 121 89 217 345), lower := (rows 7 98 388 14 49 32 64 128 256), losses := [] }

theorem u29507 : Upper (D 6) (R 6) [6,96,384,6,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29507
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29508 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 98 388 14 56 113 81 209 337), lower := (rows 7 98 388 14 56 32 64 128 256), losses := [] }

theorem u29508 : Upper (D 6) (R 6) [6,96,384,6,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29508
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29509 : PairBound 9 := { available := 102, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 98 388 25 25 102 102 230 358), lower := (rows 7 98 388 25 25 32 64 128 256), losses := [] }

theorem u29509 : Upper (D 6) (R 6) [6,96,384,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29509
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29510 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 98 388 25 26 101 101 229 357), lower := (rows 7 98 388 25 26 32 64 128 256), losses := [] }

theorem u29510 : Upper (D 6) (R 6) [6,96,384,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29510
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29511 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 98 388 25 28 99 99 227 355), lower := (rows 7 98 388 25 28 32 64 128 256), losses := [] }

theorem u29511 : Upper (D 6) (R 6) [6,96,384,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29511
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29512 : PairBound 9 := { available := 78, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 98 388 25 49 110 78 206 334), lower := (rows 7 98 388 25 49 32 64 128 256), losses := [] }

theorem u29512 : Upper (D 6) (R 6) [6,96,384,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29512
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29513 : PairBound 9 := { available := 77, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 98 388 25 50 109 77 205 333), lower := (rows 7 98 388 25 50 32 64 128 256), losses := [] }

theorem u29513 : Upper (D 6) (R 6) [6,96,384,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29513
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29514 : Route 9 := (fun mask => (mask,id))

def c29514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29514 : Upper (D 6) (R 6) [6,96,384,17,36] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,36] 13 (by decide) (choices 1) [1,2,8,64] r29514 c29514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10966
  · exact u10967
  · exact u10968
  · exact u10969

def r29515 : Route 9 := (fun mask => (mask,id))

def c29515 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29515 : Upper (D 6) (R 6) [6,96,384,17,40] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,40] 13 (by decide) (choices 1) [1,2,4,64] r29515 c29515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10970
  · exact u10971
  · exact u10972
  · exact u10973

def b29516 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 98 388 25 112 47 79 143 271), lower := (rows 7 98 388 25 112 32 64 128 256), losses := [] }

theorem u29516 : Upper (D 6) (R 6) [6,96,384,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29516
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29517 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 98 388 26 28 97 97 225 353), lower := (rows 7 98 388 26 28 32 64 128 256), losses := [] }

theorem u29517 : Upper (D 6) (R 6) [6,96,384,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29517
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29518 : Route 9 := (fun mask => (mask,id))

def c29518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29518 : Upper (D 6) (R 6) [6,96,384,18,33] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,33] 13 (by decide) (choices 1) [1,4,8,64] r29518 c29518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10974
  · exact u10975
  · exact u10976
  · exact u10977

def r29519 : Route 9 := (fun mask => (mask,id))

def c29519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29519 : Upper (D 6) (R 6) [6,96,384,18,36] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18,36] 13 (by decide) (choices 1) [1,8,64] r29519 c29519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10978
  · exact u10979
  · exact u10980

#print axioms u29519
end Delivery.IrregularNine14.P06
