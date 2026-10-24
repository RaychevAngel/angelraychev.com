import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0246
import IrregularNine14P06C0247

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32340 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 98 52 137 22 357 325 453 325), lower := (rows 11 98 52 137 22 32 64 128 256), losses := [] }

theorem u32340 : Upper (D 6) (R 6) [10,96,48,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32341 : Route 9 := (fun mask => (mask,id))

def c32341 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32341 : Upper (D 6) (R 6) [10,96,48,129,65] 13 := by
  apply FastRouting.sound _ _ [10,96,48,129,65] 13 (by decide) (choices 1) [2,4,256] r32341 c32341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14776
  · exact u14777
  · exact u14778

def b32342 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 137 82 293 325 389 261), lower := (rows 11 98 52 137 82 32 64 128 256), losses := [] }

theorem u32342 : Upper (D 6) (R 6) [10,96,48,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32343 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 20, targets := 1 },{ cop := 1, region := 20, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 98 52 137 84 295 327 391 263), lower := (rows 11 98 52 137 84 32 64 128 256), losses := [] }

theorem u32343 : Upper (D 6) (R 6) [10,96,48,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32344 : Route 9 := (fun mask => (mask,id))

def c32344 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32344 : Upper (D 6) (R 6) [10,96,48,129,257] 13 := by
  apply FastRouting.sound _ _ [10,96,48,129,257] 13 (by decide) (choices 1) [2,4,64] r32344 c32344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14779
  · exact u14780
  · exact u14781

def r32345 : Route 9 := (fun mask => (mask,id))

def c32345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32345 : Upper (D 6) (R 6) [10,96,48,129,258] 13 := by
  apply FastRouting.sound _ _ [10,96,48,129,258] 13 (by decide) (choices 1) [1,4,64] r32345 c32345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14782
  · exact u14783
  · exact u14784

def r32346 : Route 9 := (fun mask => (mask,id))

def c32346 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32346 : Upper (D 6) (R 6) [10,96,48,129,260] 13 := by
  apply FastRouting.sound _ _ [10,96,48,129,260] 13 (by decide) (choices 1) [1,2,4,64] r32346 c32346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14785
  · exact u14786
  · exact u14787
  · exact u14788

def r32347 : Route 9 := (fun mask => (mask,id))

def c32347 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32347 : Upper (D 6) (R 6) [10,96,48,129,320] 13 := by
  apply FastRouting.sound _ _ [10,96,48,129,320] 13 (by decide) (choices 1) [1,2,4] r32347 c32347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14789
  · exact u14790
  · exact u14791

def b32348 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 52 140 19 357 325 453 325), lower := (rows 11 98 52 140 19 32 64 128 256), losses := [] }

theorem u32348 : Upper (D 6) (R 6) [10,96,48,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32349 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2),(3,5)], upper := (rows 11 98 52 140 21 355 323 451 323), lower := (rows 11 98 52 140 21 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 65 129 257), good := (rows 459 66 28 140 477 0 64 128 256) }] }

theorem u32349 : Upper (D 6) (R 6) [10,96,48,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32350 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 98 52 140 22 353 321 449 321), lower := (rows 11 98 52 140 22 32 64 128 256), losses := [] }

theorem u32350 : Upper (D 6) (R 6) [10,96,48,132,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32351 : Route 9 := (fun mask => (mask,id))

def c32351 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32351 : Upper (D 6) (R 6) [10,96,48,132,65] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,65] 13 (by decide) (choices 1) [1,2,4,256] r32351 c32351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14792
  · exact u14793
  · exact u14794
  · exact u14795

def b32352 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 140 82 293 325 389 261), lower := (rows 11 98 52 140 82 32 64 128 256), losses := [] }

theorem u32352 : Upper (D 6) (R 6) [10,96,48,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32353 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 20, targets := 1 },{ cop := 1, region := 20, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 98 52 140 84 291 323 387 259), lower := (rows 11 98 52 140 84 32 64 128 256), losses := [] }

theorem u32353 : Upper (D 6) (R 6) [10,96,48,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32354 : Route 9 := (fun mask => (mask,id))

def c32354 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32354 : Upper (D 6) (R 6) [10,96,48,132,257] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,257] 13 (by decide) (choices 1) [1,2,4,64] r32354 c32354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14796
  · exact u14797
  · exact u14798
  · exact u14799

def r32355 : Route 9 := (fun mask => (mask,id))

def c32355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32355 : Upper (D 6) (R 6) [10,96,48,132,258] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,258] 13 (by decide) (choices 1) [1,4,64] r32355 c32355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14800
  · exact u14801
  · exact u14802

def r32356 : Route 9 := (fun mask => (mask,id))

def c32356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32356 : Upper (D 6) (R 6) [10,96,48,132,260] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,260] 13 (by decide) (choices 1) [1,2,64] r32356 c32356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14803
  · exact u14804
  · exact u14805

def r32357 : Route 9 := (fun mask => (mask,id))

def c32357 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32357 : Upper (D 6) (R 6) [10,96,48,132,320] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,320] 13 (by decide) (choices 1) [1,2,4] r32357 c32357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14806
  · exact u14807
  · exact u14808

def b32358 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 11 98 52 200 19 293 325 389 261), lower := (rows 11 98 52 200 19 32 64 128 256), losses := [] }

theorem u32358 : Upper (D 6) (R 6) [10,96,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32359 : Route 9 := (fun mask => (mask,id))

def c32359 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32359 : Upper (D 6) (R 6) [10,96,48,192,5] 13 := by
  apply FastRouting.sound _ _ [10,96,48,192,5] 13 (by decide) (choices 1) [1,2,4,256] r32359 c32359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14809
  · exact u14810
  · exact u14811
  · exact u14812

def b32360 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 98 52 200 22 293 325 389 261), lower := (rows 11 98 52 200 22 32 64 128 256), losses := [] }

theorem u32360 : Upper (D 6) (R 6) [10,96,48,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32361 : Route 9 := (fun mask => (mask,id))

def c32361 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32361 : Upper (D 6) (R 6) [10,96,48,192,257] 13 := by
  apply FastRouting.sound _ _ [10,96,48,192,257] 13 (by decide) (choices 1) [1,2,4] r32361 c32361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14813
  · exact u14814
  · exact u14815

def r32362 : Route 9 := (fun mask => (mask,id))

def c32362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32362 : Upper (D 6) (R 6) [10,96,48,192,258] 13 := by
  apply FastRouting.sound _ _ [10,96,48,192,258] 13 (by decide) (choices 1) [1,4] r32362 c32362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14816
  · exact u14817

def r32363 : Route 9 := (fun mask => (mask,id))

def c32363 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32363 : Upper (D 6) (R 6) [10,96,48,192,260] 13 := by
  apply FastRouting.sound _ _ [10,96,48,192,260] 13 (by decide) (choices 1) [1,2,4] r32363 c32363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14818
  · exact u14819
  · exact u14820

def b32364 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 52 392 19 101 69 197 325), lower := (rows 11 98 52 392 19 32 64 128 256), losses := [] }

theorem u32364 : Upper (D 6) (R 6) [10,96,48,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32365 : Route 9 := (fun mask => (mask,id))

def c32365 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32365 : Upper (D 6) (R 6) [10,96,48,384,5] 13 := by
  apply FastRouting.sound _ _ [10,96,48,384,5] 13 (by decide) (choices 1) [1,2,4,64] r32365 c32365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14821
  · exact u14822
  · exact u14823
  · exact u14824

def b32366 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 98 52 392 22 101 69 197 325), lower := (rows 11 98 52 392 22 32 64 128 256), losses := [] }

theorem u32366 : Upper (D 6) (R 6) [10,96,48,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32367 : Route 9 := (fun mask => (mask,id))

def c32367 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32367 : Upper (D 6) (R 6) [10,96,48,384,65] 13 := by
  apply FastRouting.sound _ _ [10,96,48,384,65] 13 (by decide) (choices 1) [1,2,4] r32367 c32367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14825
  · exact u14826
  · exact u14827

def b32368 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 392 82 37 69 133 261), lower := (rows 11 98 52 392 82 32 64 128 256), losses := [] }

theorem u32368 : Upper (D 6) (R 6) [10,96,48,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32369 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 20, targets := 1 },{ cop := 1, region := 20, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 98 52 392 84 39 71 135 263), lower := (rows 11 98 52 392 84 32 64 128 256), losses := [] }

theorem u32369 : Upper (D 6) (R 6) [10,96,48,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32370 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 133 25 22 356 356 484 356), lower := (rows 11 98 133 25 22 32 64 128 256), losses := [] }

theorem u32370 : Upper (D 6) (R 6) [10,96,129,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32371 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 133 25 50 356 324 452 324), lower := (rows 11 98 133 25 50 32 64 128 256), losses := [] }

theorem u32371 : Upper (D 6) (R 6) [10,96,129,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32372 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 452, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 98 133 25 52 358 326 454 326), lower := (rows 11 98 133 25 52 32 64 128 256), losses := [] }

theorem u32372 : Upper (D 6) (R 6) [10,96,129,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32373 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 133 25 112 294 326 390 262), lower := (rows 11 98 133 25 112 32 64 128 256), losses := [] }

theorem u32373 : Upper (D 6) (R 6) [10,96,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32374 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 133 25 274 100 100 228 356), lower := (rows 11 98 133 25 274 32 64 128 256), losses := [] }

theorem u32374 : Upper (D 6) (R 6) [10,96,129,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32375 : Route 9 := (fun mask => (mask,id))

def c32375 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32375 : Upper (D 6) (R 6) [10,96,129,17,260] 13 := by
  apply FastRouting.sound _ _ [10,96,129,17,260] 13 (by decide) (choices 1) [2,4,64] r32375 c32375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14828
  · exact u14829
  · exact u14830

def b32376 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 98 133 25 304 102 70 198 326), lower := (rows 11 98 133 25 304 32 64 128 256), losses := [] }

theorem u32376 : Upper (D 6) (R 6) [10,96,129,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32377 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 133 28 19 356 356 484 356), lower := (rows 11 98 133 28 19 32 64 128 256), losses := [] }

theorem u32377 : Upper (D 6) (R 6) [10,96,129,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32378 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 98 133 28 21 354 354 482 354), lower := (rows 11 98 133 28 21 32 64 128 256), losses := [] }

theorem u32378 : Upper (D 6) (R 6) [10,96,129,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32379 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 133 28 22 353 353 481 353), lower := (rows 11 98 133 28 22 32 64 128 256), losses := [] }

theorem u32379 : Upper (D 6) (R 6) [10,96,129,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32380 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 452, targets := 32 },{ cop := 2, region := 354, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 98 133 28 49 358 326 454 326), lower := (rows 11 98 133 28 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 65 129 257), good := (rows 463 66 453 28 477 0 64 128 256) }] }

theorem u32380 : Upper (D 6) (R 6) [10,96,129,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32381 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 98 133 28 50 357 325 453 325), lower := (rows 11 98 133 28 50 32 64 128 256), losses := [] }

theorem u32381 : Upper (D 6) (R 6) [10,96,129,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32382 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 133 28 52 355 323 451 323), lower := (rows 11 98 133 28 52 32 64 128 256), losses := [] }

theorem u32382 : Upper (D 6) (R 6) [10,96,129,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32383 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 133 28 112 295 327 391 263), lower := (rows 11 98 133 28 112 32 64 128 256), losses := [] }

theorem u32383 : Upper (D 6) (R 6) [10,96,129,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32384 : Route 9 := (fun mask => (mask,id))

def c32384 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32384 : Upper (D 6) (R 6) [10,96,129,20,257] 13 := by
  apply FastRouting.sound _ _ [10,96,129,20,257] 13 (by decide) (choices 1) [2,4,64] r32384 c32384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14831
  · exact u14832
  · exact u14833

def r32385 : Route 9 := (fun mask => (mask,id))

def c32385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32385 : Upper (D 6) (R 6) [10,96,129,20,258] 13 := by
  apply FastRouting.sound _ _ [10,96,129,20,258] 13 (by decide) (choices 1) [1,4,64] r32385 c32385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14834
  · exact u14835
  · exact u14836

def b32386 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 133 28 276 99 99 227 355), lower := (rows 11 98 133 28 276 32 64 128 256), losses := [] }

theorem u32386 : Upper (D 6) (R 6) [10,96,129,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32387 : Route 9 := (fun mask => (mask,id))

def c32387 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32387 : Upper (D 6) (R 6) [10,96,129,20,288] 13 := by
  apply FastRouting.sound _ _ [10,96,129,20,288] 13 (by decide) (choices 1) [1,2,4,64] r32387 c32387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14837
  · exact u14838
  · exact u14839
  · exact u14840

def b32388 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 98 133 44 19 372 340 468 340), lower := (rows 11 98 133 44 19 32 64 128 256), losses := [] }

theorem u32388 : Upper (D 6) (R 6) [10,96,129,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32389 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 133 44 21 370 338 466 338), lower := (rows 11 98 133 44 21 32 64 128 256), losses := [] }

theorem u32389 : Upper (D 6) (R 6) [10,96,129,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32390 : Route 9 := (fun mask => (mask,id))

def c32390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u32390 : Upper (D 6) (R 6) [10,96,129,36,6] 13 := by
  apply FastRouting.sound _ _ [10,96,129,36,6] 13 (by decide) (choices 1) [1,16,64,256] r32390 c32390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14841
  · exact u14842
  · exact u14843
  · exact u14844

def r32391 : Route 9 := (fun mask => (mask,id))

def c32391 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32391 : Upper (D 6) (R 6) [10,96,129,36,65] 13 := by
  apply FastRouting.sound _ _ [10,96,129,36,65] 13 (by decide) (choices 1) [2,4,16,256] r32391 c32391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14845
  · exact u14846
  · exact u14847
  · exact u14848

def b32392 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 133 44 82 309 341 405 277), lower := (rows 11 98 133 44 82 32 64 128 256), losses := [] }

theorem u32392 : Upper (D 6) (R 6) [10,96,129,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32393 : Route 9 := (fun mask => (mask,id))

def c32393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32393 : Upper (D 6) (R 6) [10,96,129,36,68] 13 := by
  apply FastRouting.sound _ _ [10,96,129,36,68] 13 (by decide) (choices 1) [1,2,16,256] r32393 c32393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14849
  · exact u14850
  · exact u14851
  · exact u14852

def r32394 : Route 9 := (fun mask => (mask,id))

def c32394 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32394 : Upper (D 6) (R 6) [10,96,129,36,257] 13 := by
  apply FastRouting.sound _ _ [10,96,129,36,257] 13 (by decide) (choices 1) [2,4,16,64] r32394 c32394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14853
  · exact u14854
  · exact u14855
  · exact u14856

def r32395 : Route 9 := (fun mask => (mask,id))

def c32395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32395 : Upper (D 6) (R 6) [10,96,129,36,258] 13 := by
  apply FastRouting.sound _ _ [10,96,129,36,258] 13 (by decide) (choices 1) [1,4,16,64] r32395 c32395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14857
  · exact u14858
  · exact u14859
  · exact u14860

def r32396 : Route 9 := (fun mask => (mask,id))

def c32396 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32396 : Upper (D 6) (R 6) [10,96,129,36,260] 13 := by
  apply FastRouting.sound _ _ [10,96,129,36,260] 13 (by decide) (choices 1) [1,2,16,64] r32396 c32396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14861
  · exact u14862
  · exact u14863
  · exact u14864

def r32397 : Route 9 := (fun mask => (mask,id))

def c32397 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32397 : Upper (D 6) (R 6) [10,96,129,36,320] 13 := by
  apply FastRouting.sound _ _ [10,96,129,36,320] 13 (by decide) (choices 1) [1,2,4,16] r32397 c32397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14865
  · exact u14866
  · exact u14867
  · exact u14868

def b32398 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 133 56 19 356 324 452 324), lower := (rows 11 98 133 56 19 32 64 128 256), losses := [] }

theorem u32398 : Upper (D 6) (R 6) [10,96,129,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32399 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 133 56 21 358 326 454 326), lower := (rows 11 98 133 56 21 32 64 128 256), losses := [] }

theorem u32399 : Upper (D 6) (R 6) [10,96,129,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u32399
end Delivery.IrregularNine14.P06
