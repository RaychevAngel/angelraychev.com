import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0017

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9540 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 392 52 33 82 210 338), lower := (rows 7 35 76 392 52 33 64 128 256), losses := [] }

theorem u9540 : Upper (D 6) (R 6) [6,33,72,384,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9540
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9541 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 392 52 34 81 209 337), lower := (rows 7 35 76 392 52 34 64 128 256), losses := [] }

theorem u9541 : Upper (D 6) (R 6) [6,33,72,384,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9541
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9542 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 392 52 48 67 195 323), lower := (rows 7 35 76 392 52 48 64 128 256), losses := [] }

theorem u9542 : Upper (D 6) (R 6) [6,33,72,384,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9542
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9543 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 392 52 96 83 147 275), lower := (rows 7 35 76 392 52 96 64 128 256), losses := [] }

theorem u9543 : Upper (D 6) (R 6) [6,33,72,384,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9543
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9544 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 392 81 34 116 180 308), lower := (rows 7 35 76 392 81 34 64 128 256), losses := [] }

theorem u9544 : Upper (D 6) (R 6) [6,33,72,384,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9544
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9545 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 392 81 36 114 178 306), lower := (rows 7 35 76 392 81 36 64 128 256), losses := [] }

theorem u9545 : Upper (D 6) (R 6) [6,33,72,384,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9545
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9546 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 392 81 48 102 166 294), lower := (rows 7 35 76 392 81 48 64 128 256), losses := [] }

theorem u9546 : Upper (D 6) (R 6) [6,33,72,384,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9546
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9547 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 392 82 33 116 180 308), lower := (rows 7 35 76 392 82 33 64 128 256), losses := [] }

theorem u9547 : Upper (D 6) (R 6) [6,33,72,384,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9547
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9548 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 392 82 36 113 177 305), lower := (rows 7 35 76 392 82 36 64 128 256), losses := [] }

theorem u9548 : Upper (D 6) (R 6) [6,33,72,384,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9548
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9549 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 392 82 48 101 165 293), lower := (rows 7 35 76 392 82 48 64 128 256), losses := [] }

theorem u9549 : Upper (D 6) (R 6) [6,33,72,384,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9549
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9550 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 392 112 33 86 150 278), lower := (rows 7 35 76 392 112 33 64 128 256), losses := [] }

theorem u9550 : Upper (D 6) (R 6) [6,33,72,384,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9550
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9551 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 392 112 34 85 149 277), lower := (rows 7 35 76 392 112 34 64 128 256), losses := [] }

theorem u9551 : Upper (D 6) (R 6) [6,33,72,384,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9551
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9552 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 7 35 76 392 112 36 83 147 275), lower := (rows 7 35 76 392 112 36 64 128 256), losses := [] }

theorem u9552 : Upper (D 6) (R 6) [6,33,72,384,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9552
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9553 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 392 112 48 71 135 263), lower := (rows 7 35 76 392 112 48 64 128 256), losses := [] }

theorem u9553 : Upper (D 6) (R 6) [6,33,72,384,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9553
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9554 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 26 84 40 352 480 352), lower := (rows 7 35 133 26 84 40 64 128 256), losses := [] }

theorem u9554 : Upper (D 6) (R 6) [6,33,129,18,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9554
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9555 : Route 9 := (fun mask => (mask,id))

def c9555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u9555 : Upper (D 6) (R 6) [6,33,129,18,68,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,18,68,64] 13 (by decide) (choices 1) [8,32,256] r9555 c9555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1027
  · exact u1028
  · exact u1029

def b9556 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 26 84 288 104 232 360), lower := (rows 7 35 133 26 84 288 64 128 256), losses := [] }

theorem u9556 : Upper (D 6) (R 6) [6,33,129,18,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9556
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9557 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 26 276 40 96 224 352), lower := (rows 7 35 133 26 276 40 64 128 256), losses := [] }

theorem u9557 : Upper (D 6) (R 6) [6,33,129,18,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9557
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9558 : Route 9 := (fun mask => (mask,id))

def c9558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9558 : Upper (D 6) (R 6) [6,33,129,18,260,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,18,260,64] 13 (by decide) (choices 1) [8,32] r9558 c9558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1030
  · exact u1031

def b9559 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 26 336 36 104 232 360), lower := (rows 7 35 133 26 336 36 64 128 256), losses := [] }

theorem u9559 : Upper (D 6) (R 6) [6,33,129,18,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9559
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9560 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 26 336 40 100 228 356), lower := (rows 7 35 133 26 336 40 64 128 256), losses := [] }

theorem u9560 : Upper (D 6) (R 6) [6,33,129,18,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9560
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9561 : Route 9 := (fun mask => (mask,id))

def c9561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9561 : Upper (D 6) (R 6) [6,33,129,18,320,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,18,320,64] 13 (by decide) (choices 1) [4,8,32] r9561 c9561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1032
  · exact u1033
  · exact u1034

def b9562 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 82 40 352 480 352), lower := (rows 7 35 133 28 82 40 64 128 256), losses := [] }

theorem u9562 : Upper (D 6) (R 6) [6,33,129,20,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9562
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9563 : Route 9 := (fun mask => (mask,id))

def c9563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u9563 : Upper (D 6) (R 6) [6,33,129,20,66,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20,66,64] 13 (by decide) (choices 1) [8,32,256] r9563 c9563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1035
  · exact u1036
  · exact u1037

def b9564 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 82 288 104 232 360), lower := (rows 7 35 133 28 82 288 64 128 256), losses := [] }

theorem u9564 : Upper (D 6) (R 6) [6,33,129,20,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9564
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9565 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 28 112 34 328 456 328), lower := (rows 7 35 133 28 112 34 64 128 256), losses := [] }

theorem u9565 : Upper (D 6) (R 6) [6,33,129,20,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9565
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9566 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 112 40 322 450 322), lower := (rows 7 35 133 28 112 40 64 128 256), losses := [] }

theorem u9566 : Upper (D 6) (R 6) [6,33,129,20,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9566
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9567 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 28 112 96 330 394 266), lower := (rows 7 35 133 28 112 96 64 128 256), losses := [] }

theorem u9567 : Upper (D 6) (R 6) [6,33,129,20,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9567
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9568 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 112 288 74 202 330), lower := (rows 7 35 133 28 112 288 64 128 256), losses := [] }

theorem u9568 : Upper (D 6) (R 6) [6,33,129,20,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9568
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9569 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 274 40 96 224 352), lower := (rows 7 35 133 28 274 40 64 128 256), losses := [] }

theorem u9569 : Upper (D 6) (R 6) [6,33,129,20,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9569
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9570 : Route 9 := (fun mask => (mask,id))

def c9570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9570 : Upper (D 6) (R 6) [6,33,129,20,258,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20,258,64] 13 (by decide) (choices 1) [8,32] r9570 c9570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1038
  · exact u1039

def b9571 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 28 304 34 72 200 328), lower := (rows 7 35 133 28 304 34 64 128 256), losses := [] }

theorem u9571 : Upper (D 6) (R 6) [6,33,129,20,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9571
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9572 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 304 40 66 194 322), lower := (rows 7 35 133 28 304 40 64 128 256), losses := [] }

theorem u9572 : Upper (D 6) (R 6) [6,33,129,20,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9572
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9573 : Route 9 := (fun mask => (mask,id))

def c9573 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9573 : Upper (D 6) (R 6) [6,33,129,20,288,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20,288,64] 13 (by decide) (choices 1) [2,8] r9573 c9573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1040
  · exact u1041

def b9574 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 28 336 34 104 232 360), lower := (rows 7 35 133 28 336 34 64 128 256), losses := [] }

theorem u9574 : Upper (D 6) (R 6) [6,33,129,20,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9574
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9575 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 336 40 98 226 354), lower := (rows 7 35 133 28 336 40 64 128 256), losses := [] }

theorem u9575 : Upper (D 6) (R 6) [6,33,129,20,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9575
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9576 : Route 9 := (fun mask => (mask,id))

def c9576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9576 : Upper (D 6) (R 6) [6,33,129,20,320,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20,320,64] 13 (by decide) (choices 1) [2,8,32] r9576 c9576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1042
  · exact u1043
  · exact u1044

def b9577 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 56 82 36 328 456 328), lower := (rows 7 35 133 56 82 36 64 128 256), losses := [] }

theorem u9577 : Upper (D 6) (R 6) [6,33,129,48,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9577
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9578 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 133 56 82 40 324 452 324), lower := (rows 7 35 133 56 82 40 64 128 256), losses := [] }

theorem u9578 : Upper (D 6) (R 6) [6,33,129,48,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9578
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9579 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 56 82 96 332 396 268), lower := (rows 7 35 133 56 82 96 64 128 256), losses := [] }

theorem u9579 : Upper (D 6) (R 6) [6,33,129,48,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9579
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9580 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 56 82 288 76 204 332), lower := (rows 7 35 133 56 82 288 64 128 256), losses := [] }

theorem u9580 : Upper (D 6) (R 6) [6,33,129,48,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9580
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9581 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 56 84 34 328 456 328), lower := (rows 7 35 133 56 84 34 64 128 256), losses := [] }

theorem u9581 : Upper (D 6) (R 6) [6,33,129,48,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9581
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9582 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 133 56 84 40 322 450 322), lower := (rows 7 35 133 56 84 40 64 128 256), losses := [] }

theorem u9582 : Upper (D 6) (R 6) [6,33,129,48,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9582
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9583 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 56 84 96 330 394 266), lower := (rows 7 35 133 56 84 96 64 128 256), losses := [] }

theorem u9583 : Upper (D 6) (R 6) [6,33,129,48,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9583
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9584 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 56 84 288 74 202 330), lower := (rows 7 35 133 56 84 288 64 128 256), losses := [] }

theorem u9584 : Upper (D 6) (R 6) [6,33,129,48,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9584
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9585 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 56 274 36 72 200 328), lower := (rows 7 35 133 56 274 36 64 128 256), losses := [] }

theorem u9585 : Upper (D 6) (R 6) [6,33,129,48,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9585
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9586 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 133 56 274 40 68 196 324), lower := (rows 7 35 133 56 274 40 64 128 256), losses := [] }

theorem u9586 : Upper (D 6) (R 6) [6,33,129,48,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9586
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9587 : Route 9 := (fun mask => (mask,id))

def c9587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9587 : Upper (D 6) (R 6) [6,33,129,48,258,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,48,258,64] 13 (by decide) (choices 1) [4,8] r9587 c9587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1045
  · exact u1046

def b9588 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 56 276 34 72 200 328), lower := (rows 7 35 133 56 276 34 64 128 256), losses := [] }

theorem u9588 : Upper (D 6) (R 6) [6,33,129,48,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9588
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9589 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 133 56 276 40 66 194 322), lower := (rows 7 35 133 56 276 40 64 128 256), losses := [] }

theorem u9589 : Upper (D 6) (R 6) [6,33,129,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9589
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9590 : Route 9 := (fun mask => (mask,id))

def c9590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9590 : Upper (D 6) (R 6) [6,33,129,48,260,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,48,260,64] 13 (by decide) (choices 1) [2,8] r9590 c9590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1047
  · exact u1048

def b9591 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 56 336 34 76 204 332), lower := (rows 7 35 133 56 336 34 64 128 256), losses := [] }

theorem u9591 : Upper (D 6) (R 6) [6,33,129,48,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9591
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9592 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 56 336 36 74 202 330), lower := (rows 7 35 133 56 336 36 64 128 256), losses := [] }

theorem u9592 : Upper (D 6) (R 6) [6,33,129,48,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9592
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9593 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 133 56 336 40 70 198 326), lower := (rows 7 35 133 56 336 40 64 128 256), losses := [] }

theorem u9593 : Upper (D 6) (R 6) [6,33,129,48,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9593
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9594 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 56 336 96 78 142 270), lower := (rows 7 35 133 56 336 96 64 128 256), losses := [] }

theorem u9594 : Upper (D 6) (R 6) [6,33,129,48,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9594
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9595 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 84 40 368 432 304), lower := (rows 7 35 133 74 84 40 64 128 256), losses := [] }

theorem u9595 : Upper (D 6) (R 6) [6,33,129,66,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9595
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9596 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 84 48 360 424 296), lower := (rows 7 35 133 74 84 48 64 128 256), losses := [] }

theorem u9596 : Upper (D 6) (R 6) [6,33,129,66,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9596
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9597 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 84 288 120 184 312), lower := (rows 7 35 133 74 84 288 64 128 256), losses := [] }

theorem u9597 : Upper (D 6) (R 6) [6,33,129,66,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9597
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9598 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 74 112 36 344 408 280), lower := (rows 7 35 133 74 112 36 64 128 256), losses := [] }

theorem u9598 : Upper (D 6) (R 6) [6,33,129,66,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9598
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9599 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 133 74 112 40 340 404 276), lower := (rows 7 35 133 74 112 40 64 128 256), losses := [] }

theorem u9599 : Upper (D 6) (R 6) [6,33,129,66,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9599
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9599
end Delivery.IrregularNine14.P06
