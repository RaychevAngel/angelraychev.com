import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0081

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8340 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 388 56 26 45 77 141 269), lower := (rows 35 70 388 56 26 32 64 128 256), losses := [] }

theorem u8340 : Upper (D 5) (R 5) [34,68,384,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8340
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8341 : Route 9 := (fun mask => (mask,id))

def c8341 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8341 : Upper (D 5) (R 5) [34,68,384,48,12] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,12] 13 (by decide) (choices 1) [1,2,8] r8341 c8341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4871
  · exact u4872
  · exact u4873

def b8342 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 82 44 392 19 45 77 141 269), lower := (rows 35 82 44 392 19 32 64 128 256), losses := [] }

theorem u8342 : Upper (D 5) (R 5) [34,80,40,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8342
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8343 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 82 44 392 21 47 79 143 271), lower := (rows 35 82 44 392 21 32 64 128 256), losses := [] }

theorem u8343 : Upper (D 5) (R 5) [34,80,40,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8343
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8344 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 44 392 22 45 77 141 269), lower := (rows 35 82 44 392 22 32 64 128 256), losses := [] }

theorem u8344 : Upper (D 5) (R 5) [34,80,40,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8344
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8345 : Route 9 := (fun mask => (mask,id))

def c8345 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8345 : Upper (D 5) (R 5) [34,80,40,384,9] 13 := by
  apply FastRouting.sound _ _ [34,80,40,384,9] 13 (by decide) (choices 1) [1,2,4] r8345 c8345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4874
  · exact u4875
  · exact u4876

def b8346 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 44 392 26 37 69 133 261), lower := (rows 35 82 44 392 26 32 64 128 256), losses := [] }

theorem u8346 : Upper (D 5) (R 5) [34,80,40,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8346
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8347 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 82 44 392 28 39 71 135 263), lower := (rows 35 82 44 392 28 32 64 128 256), losses := [] }

theorem u8347 : Upper (D 5) (R 5) [34,80,40,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8347
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8348 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 265 22 44 108 172 300), lower := (rows 35 82 133 265 22 32 64 128 256), losses := [] }

theorem u8348 : Upper (D 5) (R 5) [34,80,129,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8348
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m8349_8 : Upper (D 5) (R 5) [34,80,129,257,12,8] 13 :=
  permutation_upper _ _ _ [34,80,129,257,12,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4878

def r8349 : Route 9 := (fun mask => (mask,id))

def c8349 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8349 : Upper (D 5) (R 5) [34,80,129,257,12] 13 := by
  apply FastRouting.sound _ _ [34,80,129,257,12] 13 (by decide) (choices 1) [2,4,8] r8349 c8349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4877
  · exact u4878
  · exact m8349_8

def b8350 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 265 50 44 76 140 268), lower := (rows 35 82 133 265 50 32 64 128 256), losses := [] }

theorem u8350 : Upper (D 5) (R 5) [34,80,129,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8350
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8351 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 133 265 52 46 78 142 270), lower := (rows 35 82 133 265 52 32 64 128 256), losses := [] }

theorem u8351 : Upper (D 5) (R 5) [34,80,129,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8351
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8352 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 35 82 133 266 21 44 108 172 300), lower := (rows 35 82 133 266 21 32 64 128 256), losses := [] }

theorem u8352 : Upper (D 5) (R 5) [34,80,129,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8352
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8353 : Route 9 := (fun mask => (mask,id))

def c8353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8353 : Upper (D 5) (R 5) [34,80,129,258,9] 13 := by
  apply FastRouting.sound _ _ [34,80,129,258,9] 13 (by decide) (choices 1) [4,8] r8353 c8353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4879
  · exact u4880

def r8354 : Route 9 := (fun mask => (mask,id))

def c8354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8354 : Upper (D 5) (R 5) [34,80,129,258,12] 13 := by
  apply FastRouting.sound _ _ [34,80,129,258,12] 13 (by decide) (choices 1) [1,4,8] r8354 c8354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4881
  · exact u4882
  · exact u4883

def b8355 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 82 133 266 49 44 76 140 268), lower := (rows 35 82 133 266 49 32 64 128 256), losses := [] }

theorem u8355 : Upper (D 5) (R 5) [34,80,129,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8355
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8356 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 133 266 52 45 77 141 269), lower := (rows 35 82 133 266 52 32 64 128 256), losses := [] }

theorem u8356 : Upper (D 5) (R 5) [34,80,129,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8356
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8357 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 133 266 56 45 77 141 269), lower := (rows 35 82 133 266 56 32 64 128 256), losses := [] }

theorem u8357 : Upper (D 5) (R 5) [34,80,129,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8357
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8358 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 82 133 268 19 44 108 172 300), lower := (rows 35 82 133 268 19 32 64 128 256), losses := [] }

theorem u8358 : Upper (D 5) (R 5) [34,80,129,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8358
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8359 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 35 82 133 268 21 42 106 170 298), lower := (rows 35 82 133 268 21 32 64 128 256), losses := [] }

theorem u8359 : Upper (D 5) (R 5) [34,80,129,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8359
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8360 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 268 22 41 105 169 297), lower := (rows 35 82 133 268 22 32 64 128 256), losses := [] }

theorem u8360 : Upper (D 5) (R 5) [34,80,129,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8360
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8361 : Route 9 := (fun mask => (mask,id))

def c8361 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8361 : Upper (D 5) (R 5) [34,80,129,260,9] 13 := by
  apply FastRouting.sound _ _ [34,80,129,260,9] 13 (by decide) (choices 1) [2,4,8] r8361 c8361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4884
  · exact u4885
  · exact u4886

def b8362 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 268 26 45 109 173 301), lower := (rows 35 82 133 268 26 32 64 128 256), losses := [] }

theorem u8362 : Upper (D 5) (R 5) [34,80,129,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8362
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8363 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 82 133 268 28 43 107 171 299), lower := (rows 35 82 133 268 28 32 64 128 256), losses := [] }

theorem u8363 : Upper (D 5) (R 5) [34,80,129,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8363
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8364 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 82 133 268 49 46 78 142 270), lower := (rows 35 82 133 268 49 32 64 128 256), losses := [] }

theorem u8364 : Upper (D 5) (R 5) [34,80,129,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8364
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8365 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 268 50 45 77 141 269), lower := (rows 35 82 133 268 50 32 64 128 256), losses := [] }

theorem u8365 : Upper (D 5) (R 5) [34,80,129,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8365
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8366 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 133 268 52 43 75 139 267), lower := (rows 35 82 133 268 52 32 64 128 256), losses := [] }

theorem u8366 : Upper (D 5) (R 5) [34,80,129,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8366
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8367 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 133 268 56 47 79 143 271), lower := (rows 35 82 133 268 56 32 64 128 256), losses := [] }

theorem u8367 : Upper (D 5) (R 5) [34,80,129,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8367
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8368 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 82 133 296 19 44 76 140 268), lower := (rows 35 82 133 296 19 32 64 128 256), losses := [] }

theorem u8368 : Upper (D 5) (R 5) [34,80,129,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8368
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8369 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 35 82 133 296 21 46 78 142 270), lower := (rows 35 82 133 296 21 32 64 128 256), losses := [] }

theorem u8369 : Upper (D 5) (R 5) [34,80,129,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8369
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8370 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 296 22 45 77 141 269), lower := (rows 35 82 133 296 22 32 64 128 256), losses := [] }

theorem u8370 : Upper (D 5) (R 5) [34,80,129,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8370
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8371 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 82 133 296 25 46 78 142 270), lower := (rows 35 82 133 296 25 32 64 128 256), losses := [] }

theorem u8371 : Upper (D 5) (R 5) [34,80,129,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8371
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8372 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 133 296 26 45 77 141 269), lower := (rows 35 82 133 296 26 32 64 128 256), losses := [] }

theorem u8372 : Upper (D 5) (R 5) [34,80,129,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8372
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8373 : Route 9 := (fun mask => (mask,id))

def c8373 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8373 : Upper (D 5) (R 5) [34,80,129,288,12] 13 := by
  apply FastRouting.sound _ _ [34,80,129,288,12] 13 (by decide) (choices 1) [1,2,4,8] r8373 c8373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4887
  · exact u4888
  · exact u4889
  · exact u4890

def r8374 : Route 9 := (fun mask => (mask,id))

def c8374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8374 : Upper (D 5) (R 5) [34,80,130,260,5] 13 := by
  apply FastRouting.sound _ _ [34,80,130,260,5] 13 (by decide) (choices 1) [1,8] r8374 c8374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4891
  · exact u4892

def r8375 : Route 9 := (fun mask => (mask,id))

def c8375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8375 : Upper (D 5) (R 5) [34,80,130,260,9] 13 := by
  apply FastRouting.sound _ _ [34,80,130,260,9] 13 (by decide) (choices 1) [1,4,8] r8375 c8375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4893
  · exact u4894
  · exact u4895

def b8376 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 82 134 268 28 41 105 169 297), lower := (rows 35 82 134 268 28 32 64 128 256), losses := [] }

theorem u8376 : Upper (D 5) (R 5) [34,80,130,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8376
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8377 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 82 134 268 49 45 77 141 269), lower := (rows 35 82 134 268 49 32 64 128 256), losses := [] }

theorem u8377 : Upper (D 5) (R 5) [34,80,130,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8377
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8378 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 134 268 52 41 73 137 265), lower := (rows 35 82 134 268 52 32 64 128 256), losses := [] }

theorem u8378 : Upper (D 5) (R 5) [34,80,130,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8378
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8379 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 134 268 56 45 77 141 269), lower := (rows 35 82 134 268 56 32 64 128 256), losses := [] }

theorem u8379 : Upper (D 5) (R 5) [34,80,130,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8379
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8380 : Route 9 := (fun mask => (mask,id))

def c8380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8380 : Upper (D 5) (R 5) [34,80,130,288,5] 13 := by
  apply FastRouting.sound _ _ [34,80,130,288,5] 13 (by decide) (choices 1) [1,4,8] r8380 c8380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4896
  · exact u4897
  · exact u4898

def b8381 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 82 134 296 25 45 77 141 269), lower := (rows 35 82 134 296 25 32 64 128 256), losses := [] }

theorem u8381 : Upper (D 5) (R 5) [34,80,130,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8381
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8382 : Route 9 := (fun mask => (mask,id))

def c8382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8382 : Upper (D 5) (R 5) [34,80,130,288,12] 13 := by
  apply FastRouting.sound _ _ [34,80,130,288,12] 13 (by decide) (choices 1) [1,4,8] r8382 c8382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4899
  · exact u4900
  · exact u4901

def b8383 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 82 140 268 19 45 109 173 301), lower := (rows 35 82 140 268 19 32 64 128 256), losses := [] }

theorem u8383 : Upper (D 5) (R 5) [34,80,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8383
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8384 : Route 9 := (fun mask => (mask,id))

def c8384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8384 : Upper (D 5) (R 5) [34,80,136,260,5] 13 := by
  apply FastRouting.sound _ _ [34,80,136,260,5] 13 (by decide) (choices 1) [1,2,8] r8384 c8384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4902
  · exact u4903
  · exact u4904

def b8385 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 140 268 22 41 105 169 297), lower := (rows 35 82 140 268 22 32 64 128 256), losses := [] }

theorem u8385 : Upper (D 5) (R 5) [34,80,136,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8386 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 82 140 268 28 35 99 163 291), lower := (rows 35 82 140 268 28 32 64 128 256), losses := [] }

theorem u8386 : Upper (D 5) (R 5) [34,80,136,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8387 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 82 140 268 49 47 79 143 271), lower := (rows 35 82 140 268 49 32 64 128 256), losses := [] }

theorem u8387 : Upper (D 5) (R 5) [34,80,136,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8388 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 140 268 50 45 77 141 269), lower := (rows 35 82 140 268 50 32 64 128 256), losses := [] }

theorem u8388 : Upper (D 5) (R 5) [34,80,136,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8388
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8389 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 396, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 82 140 268 52 43 75 139 267), lower := (rows 35 82 140 268 52 32 64 128 256), losses := [] }

theorem u8389 : Upper (D 5) (R 5) [34,80,136,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8389
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8390 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 35 82 140 296 19 45 77 141 269), lower := (rows 35 82 140 296 19 32 64 128 256), losses := [] }

theorem u8390 : Upper (D 5) (R 5) [34,80,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8390
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8391 : Route 9 := (fun mask => (mask,id))

def c8391 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8391 : Upper (D 5) (R 5) [34,80,136,288,5] 13 := by
  apply FastRouting.sound _ _ [34,80,136,288,5] 13 (by decide) (choices 1) [1,2,4,8] r8391 c8391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4905
  · exact u4906
  · exact u4907
  · exact u4908

def b8392 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 140 296 22 45 77 141 269), lower := (rows 35 82 140 296 22 32 64 128 256), losses := [] }

theorem u8392 : Upper (D 5) (R 5) [34,80,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8393 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 82 140 296 25 39 71 135 263), lower := (rows 35 82 140 296 25 32 64 128 256), losses := [] }

theorem u8393 : Upper (D 5) (R 5) [34,80,136,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8393
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8394 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 82 140 296 26 37 69 133 261), lower := (rows 35 82 140 296 26 32 64 128 256), losses := [] }

theorem u8394 : Upper (D 5) (R 5) [34,80,136,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8394
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8395 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 82 140 296 28 39 71 135 263), lower := (rows 35 82 140 296 28 32 64 128 256), losses := [] }

theorem u8395 : Upper (D 5) (R 5) [34,80,136,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8395
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8396 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 194 52 265 19 44 76 140 268), lower := (rows 35 194 52 265 19 32 64 128 256), losses := [] }

theorem u8396 : Upper (D 5) (R 5) [34,192,48,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8396
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8397 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 20, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 194 52 265 21 46 78 142 270), lower := (rows 35 194 52 265 21 32 64 128 256), losses := [] }

theorem u8397 : Upper (D 5) (R 5) [34,192,48,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8397
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8398 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 194 52 265 22 45 77 141 269), lower := (rows 35 194 52 265 22 32 64 128 256), losses := [] }

theorem u8398 : Upper (D 5) (R 5) [34,192,48,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8399 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 194 52 265 25 46 78 142 270), lower := (rows 35 194 52 265 25 32 64 128 256), losses := [] }

theorem u8399 : Upper (D 5) (R 5) [34,192,48,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8399
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8399
end Delivery.IrregularNine14.P05
