import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0040
import IrregularNine14P06C0041

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12540 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 134 76 304 96 85 149 277), lower := (rows 11 35 134 76 304 96 64 128 256), losses := [] }

theorem u12540 : Upper (D 6) (R 6) [10,33,130,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12541 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 76 336 33 116 180 308), lower := (rows 11 35 134 76 336 33 64 128 256), losses := [] }

theorem u12541 : Upper (D 6) (R 6) [10,33,130,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12542 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 134 76 336 36 113 177 305), lower := (rows 11 35 134 76 336 36 64 128 256), losses := [] }

theorem u12542 : Upper (D 6) (R 6) [10,33,130,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12543 : Route 9 := (fun mask => (mask,id))

def c12543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12543 : Upper (D 6) (R 6) [10,33,130,68,320,16] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,320,16] 13 (by decide) (choices 1) [1,4,32] r12543 c12543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2443
  · exact u2444
  · exact u2445

def b12544 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 88 52 33 324 452 324), lower := (rows 11 35 134 88 52 33 64 128 256), losses := [] }

theorem u12544 : Upper (D 6) (R 6) [10,33,130,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12545 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 134 88 52 36 321 449 321), lower := (rows 11 35 134 88 52 36 64 128 256), losses := [] }

theorem u12545 : Upper (D 6) (R 6) [10,33,130,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12546 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 134 88 52 96 325 389 261), lower := (rows 11 35 134 88 52 96 64 128 256), losses := [] }

theorem u12546 : Upper (D 6) (R 6) [10,33,130,80,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12547 : Route 9 := (fun mask => (mask,id))

def c12547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12547 : Upper (D 6) (R 6) [10,33,130,80,36,256] 13 := by
  apply FastRouting.sound _ _ [10,33,130,80,36,256] 13 (by decide) (choices 1) [1,4] r12547 c12547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2446
  · exact u2447

def b12548 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 134 88 273 36 100 228 356), lower := (rows 11 35 134 88 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 119 183 311), good := (rows 494 486 486 504 508 484 64 128 256) },{ target := 1, region := (rows 1 0 4 14 18 36 100 164 292), good := (rows 25 505 508 88 273 492 64 128 256) }] }

theorem u12548 : Upper (D 6) (R 6) [10,33,130,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12549 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 134 88 273 96 100 164 292), lower := (rows 11 35 134 88 273 96 64 128 256), losses := [] }

theorem u12549 : Upper (D 6) (R 6) [10,33,130,80,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12550 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 88 276 33 100 228 356), lower := (rows 11 35 134 88 276 33 64 128 256), losses := [] }

theorem u12550 : Upper (D 6) (R 6) [10,33,130,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12551 : PairBound 9 := { available := 97, camps := [], pairs := [(0,6),(3,1),(4,1)], upper := (rows 11 35 134 88 276 36 97 225 353), lower := (rows 11 35 134 88 276 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 52 66 130 258), good := (rows 457 481 508 120 316 60 64 128 256) },{ target := 6, region := (rows 9 10 4 8 16 52 0 128 256), good := (rows 11 35 166 59 308 36 0 128 256) }] }

theorem u12551 : Upper (D 6) (R 6) [10,33,130,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12552 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 134 88 276 96 101 165 293), lower := (rows 11 35 134 88 276 96 64 128 256), losses := [] }

theorem u12552 : Upper (D 6) (R 6) [10,33,130,80,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12553 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 88 304 33 68 196 324), lower := (rows 11 35 134 88 304 33 64 128 256), losses := [] }

theorem u12553 : Upper (D 6) (R 6) [10,33,130,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12554 : Route 9 := (fun mask => (mask,id))

def c12554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12554 : Upper (D 6) (R 6) [10,33,130,80,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,130,80,288,4] 13 (by decide) (choices 1) [1,4] r12554 c12554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2448
  · exact u2449

def b12555 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 134 88 304 96 69 133 261), lower := (rows 11 35 134 88 304 96 64 128 256), losses := [] }

theorem u12555 : Upper (D 6) (R 6) [10,33,130,80,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12556 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 134 268 52 33 80 208 336), lower := (rows 11 35 134 268 52 33 64 128 256), losses := [] }

theorem u12556 : Upper (D 6) (R 6) [10,33,130,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12557 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 134 268 52 48 65 193 321), lower := (rows 11 35 134 268 52 48 64 128 256), losses := [] }

theorem u12557 : Upper (D 6) (R 6) [10,33,130,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12557 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12558 : Route 9 := (fun mask => (mask,id))

def c12558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12558 : Upper (D 6) (R 6) [10,33,130,260,36,64] 13 := by
  apply FastRouting.sound _ _ [10,33,130,260,36,64] 13 (by decide) (choices 1) [1,16] r12558 c12558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2450
  · exact u2451

def b12559 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 80, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 134 268 81 36 112 240 368), lower := (rows 11 35 134 268 81 36 64 128 256), losses := [] }

theorem u12559 : Upper (D 6) (R 6) [10,33,130,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12560 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 134 268 81 48 100 228 356), lower := (rows 11 35 134 268 81 48 64 128 256), losses := [] }

theorem u12560 : Upper (D 6) (R 6) [10,33,130,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12560 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12561 : Route 9 := (fun mask => (mask,id))

def c12561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12561 : Upper (D 6) (R 6) [10,33,130,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,33,130,260,65,64] 13 (by decide) (choices 1) [4,16,32] r12561 c12561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2452
  · exact u2453
  · exact u2454

def b12562 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 268 84 33 112 240 368), lower := (rows 11 35 134 268 84 33 64 128 256), losses := [] }

theorem u12562 : Upper (D 6) (R 6) [10,33,130,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12563 : PairBound 9 := { available := 97, camps := [], pairs := [(3,1),(4,1)], upper := (rows 11 35 134 268 84 48 97 225 353), lower := (rows 11 35 134 268 84 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 60 67 131 259), good := (rows 489 481 508 316 124 48 64 128 256) }] }

theorem u12563 : Upper (D 6) (R 6) [10,33,130,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12563 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12564 : Route 9 := (fun mask => (mask,id))

def c12564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12564 : Upper (D 6) (R 6) [10,33,130,260,68,64] 13 := by
  apply FastRouting.sound _ _ [10,33,130,260,68,64] 13 (by decide) (choices 1) [1,16,32] r12564 c12564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2455
  · exact u2456
  · exact u2457

def b12565 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 268 112 33 84 212 340), lower := (rows 11 35 134 268 112 33 64 128 256), losses := [] }

theorem u12565 : Upper (D 6) (R 6) [10,33,130,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12566 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 80, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 134 268 112 36 81 209 337), lower := (rows 11 35 134 268 112 36 64 128 256), losses := [] }

theorem u12566 : Upper (D 6) (R 6) [10,33,130,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12567 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 134 268 112 48 69 197 325), lower := (rows 11 35 134 268 112 48 64 128 256), losses := [] }

theorem u12567 : Upper (D 6) (R 6) [10,33,130,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12567 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12568 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 134 268 112 96 85 149 277), lower := (rows 11 35 134 268 112 96 64 128 256), losses := [] }

theorem u12568 : Upper (D 6) (R 6) [10,33,130,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12569 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 280 52 33 68 196 324), lower := (rows 11 35 134 280 52 33 64 128 256), losses := [] }

theorem u12569 : Upper (D 6) (R 6) [10,33,130,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12570 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 134 280 52 36 65 193 321), lower := (rows 11 35 134 280 52 36 64 128 256), losses := [] }

theorem u12570 : Upper (D 6) (R 6) [10,33,130,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12571 : Route 9 := (fun mask => (mask,id))

def c12571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12571 : Upper (D 6) (R 6) [10,33,130,272,36,64] 13 := by
  apply FastRouting.sound _ _ [10,33,130,272,36,64] 13 (by decide) (choices 1) [1,4] r12571 c12571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2458
  · exact u2459

def b12572 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 134 280 81 36 100 228 356), lower := (rows 11 35 134 280 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 119 183 311), good := (rows 494 486 486 504 508 484 64 128 256) },{ target := 1, region := (rows 1 0 4 14 18 36 100 164 292), good := (rows 25 505 508 280 81 492 64 128 256) }] }

theorem u12572 : Upper (D 6) (R 6) [10,33,130,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12573 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 228, targets := 1 },{ cop := 1, region := 132, targets := 64 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(2,6)], upper := (rows 11 35 134 280 81 96 100 164 292), lower := (rows 11 35 134 280 81 96 64 128 256), losses := [] }

theorem u12573 : Upper (D 6) (R 6) [10,33,130,272,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12574 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 280 84 33 100 228 356), lower := (rows 11 35 134 280 84 33 64 128 256), losses := [] }

theorem u12574 : Upper (D 6) (R 6) [10,33,130,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12575 : PairBound 9 := { available := 97, camps := [], pairs := [(0,6),(3,1),(4,1)], upper := (rows 11 35 134 280 84 36 97 225 353), lower := (rows 11 35 134 280 84 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 52 66 130 258), good := (rows 457 481 508 312 124 60 64 128 256) },{ target := 6, region := (rows 9 10 4 8 16 52 0 128 256), good := (rows 11 35 166 315 52 36 0 128 256) }] }

theorem u12575 : Upper (D 6) (R 6) [10,33,130,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12576 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 132, targets := 64 }], pairs := [(0,2),(1,2),(2,6)], upper := (rows 11 35 134 280 84 96 101 165 293), lower := (rows 11 35 134 280 84 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 112 64 128 256), good := (rows 11 35 130 315 112 96 96 128 256) }] }

theorem u12576 : Upper (D 6) (R 6) [10,33,130,272,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12577 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 280 112 33 68 196 324), lower := (rows 11 35 134 280 112 33 64 128 256), losses := [] }

theorem u12577 : Upper (D 6) (R 6) [10,33,130,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12578 : Route 9 := (fun mask => (mask,id))

def c12578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12578 : Upper (D 6) (R 6) [10,33,130,272,96,4] 13 := by
  apply FastRouting.sound _ _ [10,33,130,272,96,4] 13 (by decide) (choices 1) [1,4] r12578 c12578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2460
  · exact u2461

def b12579 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 134 280 112 96 69 133 261), lower := (rows 11 35 134 280 112 96 64 128 256), losses := [] }

theorem u12579 : Upper (D 6) (R 6) [10,33,130,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12580 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 35 134 328 21 36 112 240 368), lower := (rows 11 35 134 328 21 36 64 128 256), losses := [] }

theorem u12580 : Upper (D 6) (R 6) [10,33,130,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12581 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 134 328 21 48 100 228 356), lower := (rows 11 35 134 328 21 48 64 128 256), losses := [] }

theorem u12581 : Upper (D 6) (R 6) [10,33,130,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12581 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12582 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 134 328 21 96 116 180 308), lower := (rows 11 35 134 328 21 96 64 128 256), losses := [] }

theorem u12582 : Upper (D 6) (R 6) [10,33,130,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12583 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 328 52 33 84 212 340), lower := (rows 11 35 134 328 52 33 64 128 256), losses := [] }

theorem u12583 : Upper (D 6) (R 6) [10,33,130,320,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12584 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 134 328 52 36 81 209 337), lower := (rows 11 35 134 328 52 36 64 128 256), losses := [] }

theorem u12584 : Upper (D 6) (R 6) [10,33,130,320,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12585 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 134 328 52 48 69 197 325), lower := (rows 11 35 134 328 52 48 64 128 256), losses := [] }

theorem u12585 : Upper (D 6) (R 6) [10,33,130,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12585 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12586 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 134 328 52 96 85 149 277), lower := (rows 11 35 134 328 52 96 64 128 256), losses := [] }

theorem u12586 : Upper (D 6) (R 6) [10,33,130,320,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12587 : Route 9 := (fun mask => (mask,id))

def c12587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12587 : Upper (D 6) (R 6) [10,33,130,320,65,4] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320,65,4] 13 (by decide) (choices 1) [4,16,32] r12587 c12587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2462
  · exact u2463
  · exact u2464

def b12588 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 134 328 81 48 100 164 292), lower := (rows 11 35 134 328 81 48 64 128 256), losses := [] }

theorem u12588 : Upper (D 6) (R 6) [10,33,130,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12588 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12589 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 134 328 84 33 116 180 308), lower := (rows 11 35 134 328 84 33 64 128 256), losses := [] }

theorem u12589 : Upper (D 6) (R 6) [10,33,130,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12590 : Route 9 := (fun mask => (mask,id))

def c12590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12590 : Upper (D 6) (R 6) [10,33,130,320,68,4] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320,68,4] 13 (by decide) (choices 1) [1,16,32] r12590 c12590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2465
  · exact u2466
  · exact u2467

def r12591 : Route 9 := (fun mask => (mask,id))

def c12591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12591 : Upper (D 6) (R 6) [10,33,130,320,68,16] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320,68,16] 13 (by decide) (choices 1) [1,4,32] r12591 c12591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2468
  · exact u2469
  · exact u2470

def b12592 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 134 328 112 33 84 148 276), lower := (rows 11 35 134 328 112 33 64 128 256), losses := [] }

theorem u12592 : Upper (D 6) (R 6) [10,33,130,320,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12593 : Route 9 := (fun mask => (mask,id))

def c12593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12593 : Upper (D 6) (R 6) [10,33,130,320,96,4] 13 := by
  apply FastRouting.sound _ _ [10,33,130,320,96,4] 13 (by decide) (choices 1) [1,4,16] r12593 c12593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2471
  · exact u2472
  · exact u2473

def b12594 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 134 328 112 48 69 133 261), lower := (rows 11 35 134 328 112 48 64 128 256), losses := [] }

theorem u12594 : Upper (D 6) (R 6) [10,33,130,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12594 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12595 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 13 112 34 324 452 324), lower := (rows 11 35 148 13 112 34 64 128 256), losses := [] }

theorem u12595 : Upper (D 6) (R 6) [10,33,144,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12596 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 148 13 112 36 322 450 322), lower := (rows 11 35 148 13 112 36 64 128 256), losses := [] }

theorem u12596 : Upper (D 6) (R 6) [10,33,144,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12597 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 148 13 112 96 326 390 262), lower := (rows 11 35 148 13 112 96 64 128 256), losses := [] }

theorem u12597 : Upper (D 6) (R 6) [10,33,144,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12598 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 148 13 112 288 70 198 326), lower := (rows 11 35 148 13 112 288 64 128 256), losses := [] }

theorem u12598 : Upper (D 6) (R 6) [10,33,144,5,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12598 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12599 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 13 304 34 68 196 324), lower := (rows 11 35 148 13 304 34 64 128 256), losses := [] }

theorem u12599 : Upper (D 6) (R 6) [10,33,144,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12599
end Delivery.IrregularNine14.P06
