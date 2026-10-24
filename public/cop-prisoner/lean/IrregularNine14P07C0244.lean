import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0042
import IrregularNine14P07C0043

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14640 : Route 9 := (fun mask => (mask,id))

def c14640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14640 : Upper (D 7) (R 7) [6,257,33,66,192,128] 13 := by
  apply FastRouting.sound _ _ [6,257,33,66,192,128] 13 (by decide) (choices 1) [8,16,32] r14640 c14640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2562
  · exact u2563
  · exact u2564

def b14641 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 259 37 88 152 34 224 224 480), lower := (rows 7 259 37 88 152 34 64 128 256), losses := [] }

theorem u14641 : Upper (D 7) (R 7) [6,257,33,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14642 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 391, targets := 64 },{ cop := 0, region := 248, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 259 37 88 152 96 226 162 418), lower := (rows 7 259 37 88 152 96 64 128 256), losses := [] }

theorem u14642 : Upper (D 7) (R 7) [6,257,33,80,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14643 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 259 37 88 176 34 200 200 456), lower := (rows 7 259 37 88 176 34 64 128 256), losses := [] }

theorem u14643 : Upper (D 7) (R 7) [6,257,33,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14644 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 259 37 88 176 40 194 194 450), lower := (rows 7 259 37 88 176 40 64 128 256), losses := [] }

theorem u14644 : Upper (D 7) (R 7) [6,257,33,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14644 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14645 : Route 9 := (fun mask => (mask,id))

def c14645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14645 : Upper (D 7) (R 7) [6,257,33,80,160,64] 13 := by
  apply FastRouting.sound _ _ [6,257,33,80,160,64] 13 (by decide) (choices 1) [2,8,128] r14645 c14645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2565
  · exact u2566
  · exact u2567

def b14646 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 37 88 176 160 74 202 330), lower := (rows 7 259 37 88 176 160 64 128 256), losses := [] }

theorem u14646 : Upper (D 7) (R 7) [6,257,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14647 : PairBound 9 := { available := 152, camps := [{ cop := 8, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 259 37 104 208 34 216 152 408), lower := (rows 7 259 37 104 208 34 64 128 256), losses := [] }

theorem u14647 : Upper (D 7) (R 7) [6,257,33,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14648 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 467, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 259 37 104 208 40 210 146 402), lower := (rows 7 259 37 104 208 40 64 128 256), losses := [] }

theorem u14648 : Upper (D 7) (R 7) [6,257,33,96,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14648 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14649 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 259 37 104 208 48 202 138 394), lower := (rows 7 259 37 104 208 48 64 128 256), losses := [] }

theorem u14649 : Upper (D 7) (R 7) [6,257,33,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14649 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14650 : Route 9 := (fun mask => (mask,id))

def c14650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14650 : Upper (D 7) (R 7) [6,257,33,96,192,128] 13 := by
  apply FastRouting.sound _ _ [6,257,33,96,192,128] 13 (by decide) (choices 1) [2,8,16] r14650 c14650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2568
  · exact u2569
  · exact u2570

def b14651 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 7 259 44 25 82 96 224 160 416), lower := (rows 7 259 44 25 82 96 64 128 256), losses := [] }

theorem u14651 : Upper (D 7) (R 7) [6,257,40,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14652 : Route 9 := (fun mask => (mask,id))

def c14652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14652 : Upper (D 7) (R 7) [6,257,40,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,17,66,128] 13 (by decide) (choices 1) [32,128] r14652 c14652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2571
  · exact u2572

def b14653 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 208, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 44 25 208 34 224 224 480), lower := (rows 7 259 44 25 208 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 63 35 111 175 303), good := (rows 502 498 508 508 208 498 64 128 256) },{ target := 1, region := (rows 1 0 36 11 53 32 100 164 292), good := (rows 477 281 508 25 208 508 64 128 256) }] }

theorem u14653 : Upper (D 7) (R 7) [6,257,40,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14654 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 0, region := 240, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 259 44 25 208 96 226 162 418), lower := (rows 7 259 44 25 208 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 123 67 131 259), good := (rows 502 498 60 508 240 96 96 128 256) }] }

theorem u14654 : Upper (D 7) (R 7) [6,257,40,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14655 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 3, region := 228, targets := 3 }], pairs := [(0,6),(1,6),(2,0),(2,1)], upper := (rows 7 259 44 26 81 96 224 160 416), lower := (rows 7 259 44 26 81 96 64 128 256), losses := [] }

theorem u14655 : Upper (D 7) (R 7) [6,257,40,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14656 : Route 9 := (fun mask => (mask,id))

def c14656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14656 : Upper (D 7) (R 7) [6,257,40,18,65,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,18,65,128] 13 (by decide) (choices 1) [32,128] r14656 c14656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2573
  · exact u2574

def b14657 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 259 44 26 208 33 224 224 480), lower := (rows 7 259 44 26 208 33 64 128 256), losses := [] }

theorem u14657 : Upper (D 7) (R 7) [6,257,40,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14658 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,6),(1,6),(2,0),(4,1)], upper := (rows 7 259 44 26 208 96 225 161 417), lower := (rows 7 259 44 26 208 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 6 258 44 62 240 96 96 128 256) }] }

theorem u14658 : Upper (D 7) (R 7) [6,257,40,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14659 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 259 44 73 50 48 192 192 448), lower := (rows 7 259 44 73 50 48 64 128 256), losses := [] }

theorem u14659 : Upper (D 7) (R 7) [6,257,40,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14659 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14660 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 73 50 96 208 144 400), lower := (rows 7 259 44 73 50 96 64 128 256), losses := [] }

theorem u14660 : Upper (D 7) (R 7) [6,257,40,65,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14661 : Route 9 := (fun mask => (mask,id))

def c14661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14661 : Upper (D 7) (R 7) [6,257,40,65,34,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,34,128] 13 (by decide) (choices 1) [16,128] r14661 c14661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2575
  · exact u2576

def b14662 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 259 44 73 82 48 224 160 416), lower := (rows 7 259 44 73 82 48 64 128 256), losses := [] }

theorem u14662 : Upper (D 7) (R 7) [6,257,40,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14662 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14663 : Route 9 := (fun mask => (mask,id))

def c14663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u14663 : Upper (D 7) (R 7) [6,257,40,65,66,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,66,128] 13 (by decide) (choices 1) [16,32,128] r14663 c14663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2577
  · exact u2578
  · exact u2579

def b14664 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 208, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 44 73 112 34 208 144 400), lower := (rows 7 259 44 73 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 63 35 127 191 319), good := (rows 502 498 508 508 496 498 64 128 256) },{ target := 1, region := (rows 1 0 36 11 52 32 117 181 309), good := (rows 477 457 508 457 500 508 64 128 256) }] }

theorem u14664 : Upper (D 7) (R 7) [6,257,40,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14665 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 52, targets := 131 }], pairs := [(2,0),(2,1),(2,7)], upper := (rows 7 259 44 73 112 48 194 130 386), lower := (rows 7 259 44 73 112 48 64 128 256), losses := [] }

theorem u14665 : Upper (D 7) (R 7) [6,257,40,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14665 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14666 : Route 9 := (fun mask => (mask,id))

def c14666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14666 : Upper (D 7) (R 7) [6,257,40,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,96,128] 13 (by decide) (choices 1) [2,16,128] r14666 c14666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2580
  · exact u2581
  · exact u2582

def b14667 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 7 259 44 73 146 48 224 224 480), lower := (rows 7 259 44 73 146 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 59 127 191 319), good := (rows 502 498 492 508 498 496 64 128 256) },{ target := 1, region := (rows 1 0 4 9 16 48 116 180 308), good := (rows 461 265 492 73 496 496 64 128 256) }] }

theorem u14667 : Upper (D 7) (R 7) [6,257,40,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14667 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14668 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 73 146 96 240 176 432), lower := (rows 7 259 44 73 146 96 64 128 256), losses := [] }

theorem u14668 : Upper (D 7) (R 7) [6,257,40,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14669 : Route 9 := (fun mask => (mask,id))

def c14669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14669 : Upper (D 7) (R 7) [6,257,40,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,130,128] 13 (by decide) (choices 1) [16,32] r14669 c14669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2583
  · exact u2584

def b14670 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 208, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 44 73 176 34 208 208 464), lower := (rows 7 259 44 73 176 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 63 35 127 191 319), good := (rows 502 498 508 508 496 498 64 128 256) },{ target := 1, region := (rows 1 0 36 11 52 32 117 181 309), good := (rows 477 457 508 457 500 508 64 128 256) }] }

theorem u14670 : Upper (D 7) (R 7) [6,257,40,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14671 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 259 44 73 176 48 194 194 450), lower := (rows 7 259 44 73 176 48 64 128 256), losses := [] }

theorem u14671 : Upper (D 7) (R 7) [6,257,40,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14671 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14672 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 73 176 96 210 146 402), lower := (rows 7 259 44 73 176 96 64 128 256), losses := [] }

theorem u14672 : Upper (D 7) (R 7) [6,257,40,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14673 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 44 73 176 160 82 210 338), lower := (rows 7 259 44 73 176 160 64 128 256), losses := [] }

theorem u14673 : Upper (D 7) (R 7) [6,257,40,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14674 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 208, targets := 3 }], pairs := [(2,0),(3,1),(4,0),(4,1)], upper := (rows 7 259 44 73 208 34 240 176 432), lower := (rows 7 259 44 73 208 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 63 35 111 175 303), good := (rows 502 498 508 508 208 498 64 128 256) },{ target := 1, region := (rows 1 0 4 9 53 32 100 164 292), good := (rows 477 281 508 89 208 496 64 128 256) }] }

theorem u14674 : Upper (D 7) (R 7) [6,257,40,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14675 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 0, region := 240, targets := 1 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 7 259 44 73 208 48 226 162 418), lower := (rows 7 259 44 73 208 48 64 128 256), losses := [] }

theorem u14675 : Upper (D 7) (R 7) [6,257,40,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14675 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14676 : Route 9 := (fun mask => (mask,id))

def c14676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14676 : Upper (D 7) (R 7) [6,257,40,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,192,128] 13 (by decide) (choices 1) [2,16,32] r14676 c14676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2585
  · exact u2586
  · exact u2587

def b14677 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 259 44 74 81 48 224 160 416), lower := (rows 7 259 44 74 81 48 64 128 256), losses := [] }

theorem u14677 : Upper (D 7) (R 7) [6,257,40,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14677 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14678 : Route 9 := (fun mask => (mask,id))

def c14678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u14678 : Upper (D 7) (R 7) [6,257,40,66,65,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66,65,128] 13 (by decide) (choices 1) [16,32,128] r14678 c14678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2588
  · exact u2589
  · exact u2590

def b14679 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 2, region := 208, targets := 1 }], pairs := [(0,7),(2,7),(4,0),(4,7)], upper := (rows 7 259 44 74 112 33 208 144 400), lower := (rows 7 259 44 74 112 33 64 128 256), losses := [] }

theorem u14679 : Upper (D 7) (R 7) [6,257,40,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14680 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 259 44 74 112 48 193 129 385), lower := (rows 7 259 44 74 112 48 64 128 256), losses := [] }

theorem u14680 : Upper (D 7) (R 7) [6,257,40,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14680 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14681 : Route 9 := (fun mask => (mask,id))

def c14681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14681 : Upper (D 7) (R 7) [6,257,40,66,96,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66,96,128] 13 (by decide) (choices 1) [1,16,128] r14681 c14681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2591
  · exact u2592
  · exact u2593

def b14682 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 240, targets := 2 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 7 259 44 74 145 48 224 224 480), lower := (rows 7 259 44 74 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 9 16 48 116 180 308), good := (rows 462 266 492 74 508 500 64 128 256) }] }

theorem u14682 : Upper (D 7) (R 7) [6,257,40,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14682 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14683 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 74 145 96 240 176 432), lower := (rows 7 259 44 74 145 96 64 128 256), losses := [] }

theorem u14683 : Upper (D 7) (R 7) [6,257,40,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14684 : Route 9 := (fun mask => (mask,id))

def c14684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14684 : Upper (D 7) (R 7) [6,257,40,66,129,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66,129,128] 13 (by decide) (choices 1) [16,32] r14684 c14684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2594
  · exact u2595

def b14685 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 259 44 74 176 33 208 208 464), lower := (rows 7 259 44 74 176 33 64 128 256), losses := [] }

theorem u14685 : Upper (D 7) (R 7) [6,257,40,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14686 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 259 44 74 176 48 193 193 449), lower := (rows 7 259 44 74 176 48 64 128 256), losses := [] }

theorem u14686 : Upper (D 7) (R 7) [6,257,40,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14686 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14687 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 74 176 96 209 145 401), lower := (rows 7 259 44 74 176 96 64 128 256), losses := [] }

theorem u14687 : Upper (D 7) (R 7) [6,257,40,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14688 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 44 74 176 160 81 209 337), lower := (rows 7 259 44 74 176 160 64 128 256), losses := [] }

theorem u14688 : Upper (D 7) (R 7) [6,257,40,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14689 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 259 44 74 208 33 240 176 432), lower := (rows 7 259 44 74 208 33 64 128 256), losses := [] }

theorem u14689 : Upper (D 7) (R 7) [6,257,40,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14690 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 7 259 44 74 208 48 225 161 417), lower := (rows 7 259 44 74 208 48 64 128 256), losses := [] }

theorem u14690 : Upper (D 7) (R 7) [6,257,40,66,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14690 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14691 : Route 9 := (fun mask => (mask,id))

def c14691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14691 : Upper (D 7) (R 7) [6,257,40,66,192,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66,192,128] 13 (by decide) (choices 1) [1,16,32] r14691 c14691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2596
  · exact u2597
  · exact u2598

def b14692 : PairBound 9 := { available := 224, camps := [], pairs := [(2,0),(3,0),(3,1),(4,1)], upper := (rows 7 259 44 88 145 34 224 224 480), lower := (rows 7 259 44 88 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 119 183 311), good := (rows 486 482 492 476 508 482 64 128 256) },{ target := 1, region := (rows 1 0 4 9 17 32 100 164 292), good := (rows 477 281 492 88 153 480 64 128 256) }] }

theorem u14692 : Upper (D 7) (R 7) [6,257,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14693 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 88 145 96 226 162 418), lower := (rows 7 259 44 88 145 96 64 128 256), losses := [] }

theorem u14693 : Upper (D 7) (R 7) [6,257,40,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14694 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,0)], upper := (rows 7 259 44 88 145 160 98 226 354), lower := (rows 7 259 44 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 179 67 131 259), good := (rows 486 482 44 124 508 160 64 160 256) }] }

theorem u14694 : Upper (D 7) (R 7) [6,257,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14695 : PairBound 9 := { available := 224, camps := [], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 259 44 88 146 33 224 224 480), lower := (rows 7 259 44 88 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 17 32 100 164 292), good := (rows 478 282 492 88 146 508 64 128 256) },{ target := 1, region := (rows 1 0 20 24 16 35 119 183 311), good := (rows 485 481 492 476 508 481 64 128 256) }] }

theorem u14695 : Upper (D 7) (R 7) [6,257,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14696 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 403, targets := 64 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 259 44 88 146 96 225 161 417), lower := (rows 7 259 44 88 146 96 64 128 256), losses := [] }

theorem u14696 : Upper (D 7) (R 7) [6,257,40,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14697 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 7 259 44 88 146 160 97 225 353), lower := (rows 7 259 44 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 6 258 44 124 178 160 64 160 256) },{ target := 1, region := (rows 1 0 28 24 16 179 67 131 259), good := (rows 485 481 44 124 508 160 64 160 256) }] }

theorem u14697 : Upper (D 7) (R 7) [6,257,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14698 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5),(1,5),(2,0),(3,0)], upper := (rows 7 259 44 88 176 33 194 194 450), lower := (rows 7 259 44 88 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 52 40 48 32 67 131 259), good := (rows 454 450 60 92 188 508 64 128 256) }] }

theorem u14698 : Upper (D 7) (R 7) [6,257,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14699 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5),(1,5),(2,1),(3,1)], upper := (rows 7 259 44 88 176 34 193 193 449), lower := (rows 7 259 44 88 176 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 52 40 48 32 67 131 259), good := (rows 453 449 60 92 188 508 64 128 256) }] }

theorem u14699 : Upper (D 7) (R 7) [6,257,40,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14699
end Delivery.IrregularNine14.P07
