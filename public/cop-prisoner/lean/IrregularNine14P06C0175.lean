import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0022

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10500 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 280 81 34 69 197 325), lower := (rows 7 42 164 280 81 34 64 128 256), losses := [] }

theorem u10500 : Upper (D 6) (R 6) [6,40,160,272,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10500
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10501 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 164 280 81 36 67 195 323), lower := (rows 7 42 164 280 81 36 64 128 256), losses := [] }

theorem u10501 : Upper (D 6) (R 6) [6,40,160,272,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10501
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10502 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 42 164 280 81 96 71 135 263), lower := (rows 7 42 164 280 81 96 64 128 256), losses := [] }

theorem u10502 : Upper (D 6) (R 6) [6,40,160,272,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10502
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10503 : Route 9 := (fun mask => (mask,id))

def c10503 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10503 : Upper (D 6) (R 6) [6,40,160,272,68,1] 13 := by
  apply FastRouting.sound _ _ [6,40,160,272,68,1] 13 (by decide) (choices 1) [1,2] r10503 c10503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1335
  · exact u1336

def b10504 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 280 84 34 65 193 321), lower := (rows 7 42 164 280 84 34 64 128 256), losses := [] }

theorem u10504 : Upper (D 6) (R 6) [6,40,160,272,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10504
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10505 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 42 164 280 84 96 67 131 259), lower := (rows 7 42 164 280 84 96 64 128 256), losses := [] }

theorem u10505 : Upper (D 6) (R 6) [6,40,160,272,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10505
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10506 : Route 9 := (fun mask => (mask,id))

def c10506 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10506 : Upper (D 6) (R 6) [6,40,160,320,65,1] 13 := by
  apply FastRouting.sound _ _ [6,40,160,320,65,1] 13 (by decide) (choices 1) [2,4,16] r10506 c10506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1337
  · exact u1338
  · exact u1339

def b10507 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 328 81 34 85 149 277), lower := (rows 7 42 164 328 81 34 64 128 256), losses := [] }

theorem u10507 : Upper (D 6) (R 6) [6,40,160,320,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10507
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10508 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 164 328 81 36 83 147 275), lower := (rows 7 42 164 328 81 36 64 128 256), losses := [] }

theorem u10508 : Upper (D 6) (R 6) [6,40,160,320,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10508
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10509 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 328 81 48 71 135 263), lower := (rows 7 42 164 328 81 48 64 128 256), losses := [] }

theorem u10509 : Upper (D 6) (R 6) [6,40,160,320,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10509
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10510 : Route 9 := (fun mask => (mask,id))

def c10510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10510 : Upper (D 6) (R 6) [6,40,160,320,68,1] 13 := by
  apply FastRouting.sound _ _ [6,40,160,320,68,1] 13 (by decide) (choices 1) [1,2,16] r10510 c10510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1340
  · exact u1341
  · exact u1342

def b10511 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 328 84 34 81 145 273), lower := (rows 7 42 164 328 84 34 64 128 256), losses := [] }

theorem u10511 : Upper (D 6) (R 6) [6,40,160,320,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10511
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10512 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 328 84 48 67 131 259), lower := (rows 7 42 164 328 84 48 64 128 256), losses := [] }

theorem u10512 : Upper (D 6) (R 6) [6,40,160,320,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10512
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10513 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 25 82 33 356 420 292), lower := (rows 7 42 196 25 82 33 64 128 256), losses := [] }

theorem u10513 : Upper (D 6) (R 6) [6,40,192,17,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10513
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10514 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 7 42 196 25 82 36 353 417 289), lower := (rows 7 42 196 25 82 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 228 58 82 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 16 37 0 137 265), good := (rows 423 426 164 443 18 36 0 128 256) }] }

theorem u10514 : Upper (D 6) (R 6) [6,40,192,17,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10514
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10515 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(1,6),(2,1)], upper := (rows 7 42 196 25 82 288 101 165 293), lower := (rows 7 42 196 25 82 288 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 297 0 129 257), good := (rows 423 42 132 443 18 288 0 128 288) }] }

theorem u10515 : Upper (D 6) (R 6) [6,40,192,17,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10515
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10516 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 25 274 33 100 228 356), lower := (rows 7 42 196 25 274 33 64 128 256), losses := [] }

theorem u10516 : Upper (D 6) (R 6) [6,40,192,17,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10516
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10517 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 7 42 196 25 274 36 97 225 353), lower := (rows 7 42 196 25 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 228 58 274 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 16 37 0 128 256), good := (rows 39 42 164 59 274 36 0 128 256) }] }

theorem u10517 : Upper (D 6) (R 6) [6,40,192,17,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10517
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10518 : Route 9 := (fun mask => (mask,id))

def c10518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10518 : Upper (D 6) (R 6) [6,40,192,17,258,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,258,64] 13 (by decide) (choices 1) [1,4,32] r10518 c10518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1343
  · exact u1344
  · exact u1345

def b10519 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 196 25 276 33 98 226 354), lower := (rows 7 42 196 25 276 33 64 128 256), losses := [] }

theorem u10519 : Upper (D 6) (R 6) [6,40,192,17,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10519
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10520 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 196 25 276 34 97 225 353), lower := (rows 7 42 196 25 276 34 64 128 256), losses := [] }

theorem u10520 : Upper (D 6) (R 6) [6,40,192,17,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10520
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10521 : Route 9 := (fun mask => (mask,id))

def c10521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10521 : Upper (D 6) (R 6) [6,40,192,17,260,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,260,64] 13 (by decide) (choices 1) [1,2,32] r10521 c10521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1346
  · exact u1347
  · exact u1348

def b10522 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 7 42 196 25 304 33 70 198 326), lower := (rows 7 42 196 25 304 33 64 128 256), losses := [] }

theorem u10522 : Upper (D 6) (R 6) [6,40,192,17,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10522
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10523 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 25 304 34 69 197 325), lower := (rows 7 42 196 25 304 34 64 128 256), losses := [] }

theorem u10523 : Upper (D 6) (R 6) [6,40,192,17,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10523
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10524 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 196 25 304 36 67 195 323), lower := (rows 7 42 196 25 304 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 228 58 304 36 64 128 256) }] }

theorem u10524 : Upper (D 6) (R 6) [6,40,192,17,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10524
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10525 : Route 9 := (fun mask => (mask,id))

def c10525 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10525 : Upper (D 6) (R 6) [6,40,192,17,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,288,64] 13 (by decide) (choices 1) [1,2,4] r10525 c10525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1349
  · exact u1350
  · exact u1351

def b10526 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 25 336 33 102 166 294), lower := (rows 7 42 196 25 336 33 64 128 256), losses := [] }

theorem u10526 : Upper (D 6) (R 6) [6,40,192,17,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10526
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10527 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 25 336 34 101 165 293), lower := (rows 7 42 196 25 336 34 64 128 256), losses := [] }

theorem u10527 : Upper (D 6) (R 6) [6,40,192,17,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10527
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10528 : Route 9 := (fun mask => (mask,id))

def c10528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10528 : Upper (D 6) (R 6) [6,40,192,17,320,4] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,320,4] 13 (by decide) (choices 1) [1,2,32] r10528 c10528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1352
  · exact u1353
  · exact u1354

def b10529 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 42 196 26 273 33 100 228 356), lower := (rows 7 42 196 26 273 33 64 128 256), losses := [] }

theorem u10529 : Upper (D 6) (R 6) [6,40,192,18,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10529
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10530 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 196 26 273 36 97 225 353), lower := (rows 7 42 196 26 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 64 128 256), good := (rows 38 42 228 26 314 36 64 128 256) }] }

theorem u10530 : Upper (D 6) (R 6) [6,40,192,18,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10530
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10531 : Route 9 := (fun mask => (mask,id))

def c10531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10531 : Upper (D 6) (R 6) [6,40,192,18,257,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,257,64] 13 (by decide) (choices 1) [1,4,32] r10531 c10531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1355
  · exact u1356
  · exact u1357

def b10532 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 196 26 276 33 97 225 353), lower := (rows 7 42 196 26 276 33 64 128 256), losses := [] }

theorem u10532 : Upper (D 6) (R 6) [6,40,192,18,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10532
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10533 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 196 26 276 96 97 161 289), lower := (rows 7 42 196 26 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 100 64 128 256), good := (rows 38 42 228 26 318 96 96 128 256) }] }

theorem u10533 : Upper (D 6) (R 6) [6,40,192,18,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10533
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10534 : Route 9 := (fun mask => (mask,id))

def c10534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10534 : Upper (D 6) (R 6) [6,40,192,18,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,320,1] 13 (by decide) (choices 1) [1,4,32] r10534 c10534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1358
  · exact u1359
  · exact u1360

def r10535 : Route 9 := (fun mask => (mask,id))

def c10535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10535 : Upper (D 6) (R 6) [6,40,192,18,320,4] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,320,4] 13 (by decide) (choices 1) [1,32] r10535 c10535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1361
  · exact u1362

def b10536 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 196 28 273 33 98 226 354), lower := (rows 7 42 196 28 273 33 64 128 256), losses := [] }

theorem u10536 : Upper (D 6) (R 6) [6,40,192,20,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10536
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10537 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 196 28 273 34 97 225 353), lower := (rows 7 42 196 28 273 34 64 128 256), losses := [] }

theorem u10537 : Upper (D 6) (R 6) [6,40,192,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10537
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10538 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 42 196 28 273 96 99 163 291), lower := (rows 7 42 196 28 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 100 64 128 256), good := (rows 38 42 228 62 272 96 96 128 256) },{ target := 2, region := (rows 1 10 0 8 17 117 65 129 257), good := (rows 499 42 224 58 497 96 96 128 256) }] }

theorem u10538 : Upper (D 6) (R 6) [6,40,192,20,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10538
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10539 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 7 42 196 28 274 33 97 225 353), lower := (rows 7 42 196 28 274 33 64 128 256), losses := [] }

theorem u10539 : Upper (D 6) (R 6) [6,40,192,20,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10539
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10540 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(2,1),(4,2)], upper := (rows 7 42 196 28 274 96 97 161 289), lower := (rows 7 42 196 28 274 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 100 64 128 256), good := (rows 38 42 228 62 274 96 96 128 256) }] }

theorem u10540 : Upper (D 6) (R 6) [6,40,192,20,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10540
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10541 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 50, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 7 42 196 73 49 34 340 404 276), lower := (rows 7 42 196 73 49 34 64 128 256), losses := [] }

theorem u10541 : Upper (D 6) (R 6) [6,40,192,65,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10541
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10542 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 330, targets := 4 },{ cop := 0, region := 48, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 42 196 73 49 36 338 402 274), lower := (rows 7 42 196 73 49 36 64 128 256), losses := [] }

theorem u10542 : Upper (D 6) (R 6) [6,40,192,65,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10542
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10543 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 50, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 42 196 73 49 48 326 390 262), lower := (rows 7 42 196 73 49 48 64 128 256), losses := [] }

theorem u10543 : Upper (D 6) (R 6) [6,40,192,65,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10543
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10544 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 73 49 288 86 150 278), lower := (rows 7 42 196 73 49 288 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 25 313 0 129 257), good := (rows 439 58 132 443 433 288 0 128 288) }] }

theorem u10544 : Upper (D 6) (R 6) [6,40,192,65,33,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10544
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10545 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 73 52 33 338 402 274), lower := (rows 7 42 196 73 52 33 64 128 256), losses := [] }

theorem u10545 : Upper (D 6) (R 6) [6,40,192,65,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10545
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10546 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 73 52 34 337 401 273), lower := (rows 7 42 196 73 52 34 64 128 256), losses := [] }

theorem u10546 : Upper (D 6) (R 6) [6,40,192,65,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10546
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10547 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 73 52 48 323 387 259), lower := (rows 7 42 196 73 52 48 64 128 256), losses := [] }

theorem u10547 : Upper (D 6) (R 6) [6,40,192,65,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10547
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10548 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 73 52 288 83 147 275), lower := (rows 7 42 196 73 52 288 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 17 299 0 137 265), good := (rows 439 426 132 443 52 288 0 128 288) }] }

theorem u10548 : Upper (D 6) (R 6) [6,40,192,65,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10548
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10549 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 73 273 34 116 180 308), lower := (rows 7 42 196 73 273 34 64 128 256), losses := [] }

theorem u10549 : Upper (D 6) (R 6) [6,40,192,65,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10549
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10550 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 7 42 196 73 273 36 114 178 306), lower := (rows 7 42 196 73 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 228 106 304 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 25 37 0 139 267), good := (rows 439 442 164 443 433 36 0 128 256) }] }

theorem u10550 : Upper (D 6) (R 6) [6,40,192,65,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10550
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10551 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 304, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(4,6)], upper := (rows 7 42 196 73 273 48 102 166 294), lower := (rows 7 42 196 73 273 48 64 128 256), losses := [] }

theorem u10551 : Upper (D 6) (R 6) [6,40,192,65,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10551
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10552 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 73 274 33 116 180 308), lower := (rows 7 42 196 73 274 33 64 128 256), losses := [] }

theorem u10552 : Upper (D 6) (R 6) [6,40,192,65,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10552
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10553 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 7 42 196 73 274 36 113 177 305), lower := (rows 7 42 196 73 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 228 106 274 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 27 37 0 137 265), good := (rows 439 442 164 443 274 36 0 128 256) }] }

theorem u10553 : Upper (D 6) (R 6) [6,40,192,65,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10553
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10554 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 73 274 48 101 165 293), lower := (rows 7 42 196 73 274 48 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 25 59 0 129 257), good := (rows 439 58 132 443 306 48 0 128 256) }] }

theorem u10554 : Upper (D 6) (R 6) [6,40,192,65,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10554
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10555 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 73 276 33 114 178 306), lower := (rows 7 42 196 73 276 33 64 128 256), losses := [] }

theorem u10555 : Upper (D 6) (R 6) [6,40,192,65,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10555
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10556 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 73 276 34 113 177 305), lower := (rows 7 42 196 73 276 34 64 128 256), losses := [] }

theorem u10556 : Upper (D 6) (R 6) [6,40,192,65,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10556
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10557 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 73 276 48 99 163 291), lower := (rows 7 42 196 73 276 48 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 17 57 0 137 265), good := (rows 439 426 132 443 308 48 0 128 256) }] }

theorem u10557 : Upper (D 6) (R 6) [6,40,192,65,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10557
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10558 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 73 304 33 86 150 278), lower := (rows 7 42 196 73 304 33 64 128 256), losses := [] }

theorem u10558 : Upper (D 6) (R 6) [6,40,192,65,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10558
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10559 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 73 304 34 85 149 277), lower := (rows 7 42 196 73 304 34 64 128 256), losses := [] }

theorem u10559 : Upper (D 6) (R 6) [6,40,192,65,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10559
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10559
end Delivery.IrregularNine14.P06
