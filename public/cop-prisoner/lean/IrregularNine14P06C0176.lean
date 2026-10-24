import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0022
import IrregularNine14P06C0023

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10560 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 7 42 196 73 304 36 83 147 275), lower := (rows 7 42 196 73 304 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 228 106 304 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 27 37 0 137 265), good := (rows 439 442 164 443 304 36 0 128 256) }] }

theorem u10560 : Upper (D 6) (R 6) [6,40,192,65,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10560
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10561 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 196 73 304 48 71 135 263), lower := (rows 7 42 196 73 304 48 64 128 256), losses := [] }

theorem u10561 : Upper (D 6) (R 6) [6,40,192,65,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10561
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10562 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 304, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(2,0),(4,6)], upper := (rows 7 42 196 88 273 33 102 166 294), lower := (rows 7 42 196 88 273 33 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 49 64 128 256), good := (rows 35 42 192 122 305 33 64 128 256) }] }

theorem u10562 : Upper (D 6) (R 6) [6,40,192,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10562
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10563 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 88 273 34 101 165 293), lower := (rows 7 42 196 88 273 34 64 128 256), losses := [] }

theorem u10563 : Upper (D 6) (R 6) [6,40,192,80,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10563
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10564 : Route 9 := (fun mask => (mask,id))

def c10564 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10564 : Upper (D 6) (R 6) [6,40,192,80,257,4] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,257,4] 13 (by decide) (choices 1) [1,2,32] r10564 c10564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1363
  · exact u1364
  · exact u1365

def r10565 : Route 9 := (fun mask => (mask,id))

def c10565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10565 : Upper (D 6) (R 6) [6,40,192,80,258,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,258,1] 13 (by decide) (choices 1) [1,4,32] r10565 c10565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1366
  · exact u1367
  · exact u1368

def r10566 : Route 9 := (fun mask => (mask,id))

def c10566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10566 : Upper (D 6) (R 6) [6,40,192,80,258,4] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,258,4] 13 (by decide) (choices 1) [1,32] r10566 c10566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1369
  · exact u1370

def r10567 : Route 9 := (fun mask => (mask,id))

def c10567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10567 : Upper (D 6) (R 6) [6,40,192,80,260,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,260,1] 13 (by decide) (choices 1) [1,2,32] r10567 c10567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1371
  · exact u1372
  · exact u1373

def b10568 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 88 276 34 97 161 289), lower := (rows 7 42 196 88 276 34 64 128 256), losses := [] }

theorem u10568 : Upper (D 6) (R 6) [6,40,192,80,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10568
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10569 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 50, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 7 42 196 265 49 34 84 212 340), lower := (rows 7 42 196 265 49 34 64 128 256), losses := [] }

theorem u10569 : Upper (D 6) (R 6) [6,40,192,257,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10569
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10570 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 4, region := 330, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 42 196 265 49 36 82 210 338), lower := (rows 7 42 196 265 49 36 64 128 256), losses := [] }

theorem u10570 : Upper (D 6) (R 6) [6,40,192,257,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10570
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10571 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 50, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 42 196 265 49 48 70 198 326), lower := (rows 7 42 196 265 49 48 64 128 256), losses := [] }

theorem u10571 : Upper (D 6) (R 6) [6,40,192,257,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10571
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10572 : Route 9 := (fun mask => (mask,id))

def c10572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10572 : Upper (D 6) (R 6) [6,40,192,257,33,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,33,64] 13 (by decide) (choices 1) [2,4,16] r10572 c10572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1374
  · exact u1375
  · exact u1376

def b10573 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(4,1),(4,6)], upper := (rows 7 42 196 265 52 33 82 210 338), lower := (rows 7 42 196 265 52 33 64 128 256), losses := [] }

theorem u10573 : Upper (D 6) (R 6) [6,40,192,257,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10573
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10574 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 265 52 34 81 209 337), lower := (rows 7 42 196 265 52 34 64 128 256), losses := [] }

theorem u10574 : Upper (D 6) (R 6) [6,40,192,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10574
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10575 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 265 52 48 67 195 323), lower := (rows 7 42 196 265 52 48 64 128 256), losses := [] }

theorem u10575 : Upper (D 6) (R 6) [6,40,192,257,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10575
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10576 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 267, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 196 265 52 96 83 147 275), lower := (rows 7 42 196 265 52 96 64 128 256), losses := [] }

theorem u10576 : Upper (D 6) (R 6) [6,40,192,257,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10576
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10577 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 265 81 34 116 180 308), lower := (rows 7 42 196 265 81 34 64 128 256), losses := [] }

theorem u10577 : Upper (D 6) (R 6) [6,40,192,257,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10577
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10578 : PairBound 9 := { available := 50, camps := [], pairs := [(1,0),(1,6),(3,6)], upper := (rows 7 42 196 265 81 36 114 178 306), lower := (rows 7 42 196 265 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 228 298 112 36 64 128 256) },{ target := 6, region := (rows 1 26 4 24 16 37 0 144 272), good := (rows 39 42 164 299 443 36 0 128 256) }] }

theorem u10578 : Upper (D 6) (R 6) [6,40,192,257,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10578
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10579 : Route 9 := (fun mask => (mask,id))

def c10579 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10579 : Upper (D 6) (R 6) [6,40,192,257,65,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,65,16] 13 (by decide) (choices 1) [2,4,32] r10579 c10579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1377
  · exact u1378
  · exact u1379

def b10580 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 265 82 33 116 180 308), lower := (rows 7 42 196 265 82 33 64 128 256), losses := [] }

theorem u10580 : Upper (D 6) (R 6) [6,40,192,257,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10580
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10581 : Route 9 := (fun mask => (mask,id))

def c10581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10581 : Upper (D 6) (R 6) [6,40,192,257,66,4] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,66,4] 13 (by decide) (choices 1) [1,16,32] r10581 c10581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1380
  · exact u1381
  · exact u1382

def r10582 : Route 9 := (fun mask => (mask,id))

def c10582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10582 : Upper (D 6) (R 6) [6,40,192,257,66,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,66,16] 13 (by decide) (choices 1) [1,4,32] r10582 c10582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1383
  · exact u1384
  · exact u1385

def b10583 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 196 265 112 33 86 150 278), lower := (rows 7 42 196 265 112 33 64 128 256), losses := [] }

theorem u10583 : Upper (D 6) (R 6) [6,40,192,257,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10583
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10584 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 265 112 34 85 149 277), lower := (rows 7 42 196 265 112 34 64 128 256), losses := [] }

theorem u10584 : Upper (D 6) (R 6) [6,40,192,257,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10584
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10585 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 7 42 196 265 112 36 83 147 275), lower := (rows 7 42 196 265 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 20 37 64 128 256), good := (rows 54 42 244 298 112 52 64 128 256) }] }

theorem u10585 : Upper (D 6) (R 6) [6,40,192,257,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10585
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10586 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 265 112 48 71 135 263), lower := (rows 7 42 196 265 112 48 64 128 256), losses := [] }

theorem u10586 : Upper (D 6) (R 6) [6,40,192,257,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10586
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10587 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 48, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 196 266 52 33 81 209 337), lower := (rows 7 42 196 266 52 33 64 128 256), losses := [] }

theorem u10587 : Upper (D 6) (R 6) [6,40,192,258,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10587
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10588 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 266 52 48 65 193 321), lower := (rows 7 42 196 266 52 48 64 128 256), losses := [] }

theorem u10588 : Upper (D 6) (R 6) [6,40,192,258,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10588
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10589 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 267, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 196 266 52 96 81 145 273), lower := (rows 7 42 196 266 52 96 64 128 256), losses := [] }

theorem u10589 : Upper (D 6) (R 6) [6,40,192,258,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10589
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10590 : Route 9 := (fun mask => (mask,id))

def c10590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10590 : Upper (D 6) (R 6) [6,40,192,258,65,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,65,1] 13 (by decide) (choices 1) [4,16,32] r10590 c10590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1386
  · exact u1387
  · exact u1388

def b10591 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 7 42 196 266 81 36 113 177 305), lower := (rows 7 42 196 266 81 36 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 37 0 144 272), good := (rows 39 42 164 266 443 36 0 128 256) }] }

theorem u10591 : Upper (D 6) (R 6) [6,40,192,258,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10591
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10592 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 42 196 266 81 48 101 165 293), lower := (rows 7 42 196 266 81 48 64 128 256), losses := [] }

theorem u10592 : Upper (D 6) (R 6) [6,40,192,258,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10592
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10593 : Route 9 := (fun mask => (mask,id))

def c10593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10593 : Upper (D 6) (R 6) [6,40,192,258,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,96,1] 13 (by decide) (choices 1) [1,4,16] r10593 c10593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1389
  · exact u1390
  · exact u1391

def b10594 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 2, region := 48, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 7 42 196 266 112 36 81 145 273), lower := (rows 7 42 196 266 112 36 64 128 256), losses := [] }

theorem u10594 : Upper (D 6) (R 6) [6,40,192,258,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10594
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10595 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 266 112 48 69 133 261), lower := (rows 7 42 196 266 112 48 64 128 256), losses := [] }

theorem u10595 : Upper (D 6) (R 6) [6,40,192,258,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10595
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10596 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 42 196 268 49 33 82 210 338), lower := (rows 7 42 196 268 49 33 64 128 256), losses := [] }

theorem u10596 : Upper (D 6) (R 6) [6,40,192,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10596
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10597 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 42 196 268 49 34 81 209 337), lower := (rows 7 42 196 268 49 34 64 128 256), losses := [] }

theorem u10597 : Upper (D 6) (R 6) [6,40,192,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10597
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10598 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 268 49 48 67 195 323), lower := (rows 7 42 196 268 49 48 64 128 256), losses := [] }

theorem u10598 : Upper (D 6) (R 6) [6,40,192,260,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10598
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10599 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 7 42 196 268 49 96 83 147 275), lower := (rows 7 42 196 268 49 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 100 64 128 256), good := (rows 38 42 228 302 48 96 96 128 256) },{ target := 1, region := (rows 1 0 4 8 17 100 64 128 256), good := (rows 53 40 228 300 49 96 96 128 256) }] }

theorem u10599 : Upper (D 6) (R 6) [6,40,192,260,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10599
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10600 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 196 268 81 33 114 178 306), lower := (rows 7 42 196 268 81 33 64 128 256), losses := [] }

theorem u10600 : Upper (D 6) (R 6) [6,40,192,260,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10600
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10601 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 196 268 81 34 113 177 305), lower := (rows 7 42 196 268 81 34 64 128 256), losses := [] }

theorem u10601 : Upper (D 6) (R 6) [6,40,192,260,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10601
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10602 : Route 9 := (fun mask => (mask,id))

def c10602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10602 : Upper (D 6) (R 6) [6,40,192,260,65,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260,65,16] 13 (by decide) (choices 1) [1,2,32] r10602 c10602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1392
  · exact u1393
  · exact u1394

def b10603 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 196 268 82 33 113 177 305), lower := (rows 7 42 196 268 82 33 64 128 256), losses := [] }

theorem u10603 : Upper (D 6) (R 6) [6,40,192,260,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10603
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10604 : Route 9 := (fun mask => (mask,id))

def c10604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10604 : Upper (D 6) (R 6) [6,40,192,260,66,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260,66,16] 13 (by decide) (choices 1) [1,32] r10604 c10604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1395
  · exact u1396

def b10605 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 196 268 112 33 83 147 275), lower := (rows 7 42 196 268 112 33 64 128 256), losses := [] }

theorem u10605 : Upper (D 6) (R 6) [6,40,192,260,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10605
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10606 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 196 268 112 34 81 145 273), lower := (rows 7 42 196 268 112 34 64 128 256), losses := [] }

theorem u10606 : Upper (D 6) (R 6) [6,40,192,260,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10606
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10607 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 196 268 112 48 67 131 259), lower := (rows 7 42 196 268 112 48 64 128 256), losses := [] }

theorem u10607 : Upper (D 6) (R 6) [6,40,192,260,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10607
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10608 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(4,1),(4,6)], upper := (rows 7 42 196 280 52 33 67 195 323), lower := (rows 7 42 196 280 52 33 64 128 256), losses := [] }

theorem u10608 : Upper (D 6) (R 6) [6,40,192,272,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10608
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10609 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 280 52 34 65 193 321), lower := (rows 7 42 196 280 52 34 64 128 256), losses := [] }

theorem u10609 : Upper (D 6) (R 6) [6,40,192,272,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10609
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10610 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 267, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 196 280 52 96 67 131 259), lower := (rows 7 42 196 280 52 96 64 128 256), losses := [] }

theorem u10610 : Upper (D 6) (R 6) [6,40,192,272,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10610
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10611 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 196, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 7 42 196 280 81 33 102 166 294), lower := (rows 7 42 196 280 81 33 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 49 64 128 256), good := (rows 35 42 192 314 113 33 64 128 256) },{ target := 6, region := (rows 1 26 4 24 16 49 0 129 257), good := (rows 423 42 132 314 443 417 0 128 256) }] }

theorem u10611 : Upper (D 6) (R 6) [6,40,192,272,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10611
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10612 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 280 81 34 101 165 293), lower := (rows 7 42 196 280 81 34 64 128 256), losses := [] }

theorem u10612 : Upper (D 6) (R 6) [6,40,192,272,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10612
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10613 : Route 9 := (fun mask => (mask,id))

def c10613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10613 : Upper (D 6) (R 6) [6,40,192,272,65,4] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,65,4] 13 (by decide) (choices 1) [1,2,32] r10613 c10613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1397
  · exact u1398
  · exact u1399

def r10614 : Route 9 := (fun mask => (mask,id))

def c10614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10614 : Upper (D 6) (R 6) [6,40,192,272,66,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,66,1] 13 (by decide) (choices 1) [1,4,32] r10614 c10614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1400
  · exact u1401
  · exact u1402

def r10615 : Route 9 := (fun mask => (mask,id))

def c10615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10615 : Upper (D 6) (R 6) [6,40,192,272,66,4] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,66,4] 13 (by decide) (choices 1) [1,32] r10615 c10615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1403
  · exact u1404

def r10616 : Route 9 := (fun mask => (mask,id))

def c10616 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10616 : Upper (D 6) (R 6) [6,40,192,272,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,96,1] 13 (by decide) (choices 1) [1,2,4] r10616 c10616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1405
  · exact u1406
  · exact u1407

def b10617 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 280 112 34 69 133 261), lower := (rows 7 42 196 280 112 34 64 128 256), losses := [] }

theorem u10617 : Upper (D 6) (R 6) [6,40,192,272,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10617
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10618 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(0,5),(2,5),(4,0)], upper := (rows 7 42 196 280 112 36 67 131 259), lower := (rows 7 42 196 280 112 36 64 128 256), losses := [] }

theorem u10618 : Upper (D 6) (R 6) [6,40,192,272,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10618
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10619 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 196 328 49 33 86 150 278), lower := (rows 7 42 196 328 49 33 64 128 256), losses := [] }

theorem u10619 : Upper (D 6) (R 6) [6,40,192,320,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10619
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10619
end Delivery.IrregularNine14.P06
