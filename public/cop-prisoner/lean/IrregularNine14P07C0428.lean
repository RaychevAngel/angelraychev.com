import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0150

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25680 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 14 73 176 160 82 210 338), lower := (rows 37 259 14 73 176 160 64 128 256), losses := [] }

theorem u25680 : Upper (D 7) (R 7) [36,257,10,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25681 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 14 73 208 34 240 176 432), lower := (rows 37 259 14 73 208 34 64 128 256), losses := [] }

theorem u25681 : Upper (D 7) (R 7) [36,257,10,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25682 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 386, targets := 64 },{ cop := 1, region := 240, targets := 1 }], pairs := [(1,6),(2,6),(4,0)], upper := (rows 37 259 14 73 208 48 226 162 418), lower := (rows 37 259 14 73 208 48 64 128 256), losses := [{ target := 6, region := (rows 1 11 12 8 16 48 0 129 257), good := (rows 423 387 14 399 176 48 0 128 256) }] }

theorem u25682 : Upper (D 7) (R 7) [36,257,10,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25682 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25683 : Route 9 := (fun mask => (mask,id))

def c25683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25683 : Upper (D 7) (R 7) [36,257,10,65,192,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,192,128] 13 (by decide) (choices 1) [2,16,32] r25683 c25683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9017
  · exact u9018
  · exact u9019

def b25684 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 14 88 145 34 224 224 480), lower := (rows 37 259 14 88 145 34 64 128 256), losses := [] }

theorem u25684 : Upper (D 7) (R 7) [36,257,10,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25685 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 402, targets := 64 }], pairs := [(0,1),(1,6),(2,6),(4,6)], upper := (rows 37 259 14 88 145 96 226 162 418), lower := (rows 37 259 14 88 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 257 45 120 145 96 96 128 256) },{ target := 6, region := (rows 1 19 12 8 19 32 0 129 257), good := (rows 439 403 30 30 403 32 0 128 256) }] }

theorem u25685 : Upper (D 7) (R 7) [36,257,10,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25686 : Route 9 := (fun mask => (mask,id))

def c25686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25686 : Upper (D 7) (R 7) [36,257,10,80,129,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,80,129,128] 13 (by decide) (choices 1) [2,32] r25686 c25686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9020
  · exact u9021

def b25687 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 14 88 146 33 224 224 480), lower := (rows 37 259 14 88 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 22 10 18 32 97 161 289), good := (rows 484 478 30 92 158 480 64 128 256) }] }

theorem u25687 : Upper (D 7) (R 7) [36,257,10,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25688 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,6)], upper := (rows 37 259 14 88 146 96 225 161 417), lower := (rows 37 259 14 88 146 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 127 71 135 263), good := (rows 485 481 493 120 504 96 96 128 256) }] }

theorem u25688 : Upper (D 7) (R 7) [36,257,10,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25689 : Route 9 := (fun mask => (mask,id))

def c25689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25689 : Upper (D 7) (R 7) [36,257,10,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,80,130,128] 13 (by decide) (choices 1) [1,32] r25689 c25689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9022
  · exact u9023

def b25690 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 14 88 176 33 194 194 450), lower := (rows 37 259 14 88 176 33 64 128 256), losses := [] }

theorem u25690 : Upper (D 7) (R 7) [36,257,10,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25691 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 14 88 176 34 193 193 449), lower := (rows 37 259 14 88 176 34 64 128 256), losses := [] }

theorem u25691 : Upper (D 7) (R 7) [36,257,10,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25692 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,1),(1,5),(1,6),(4,6)], upper := (rows 37 259 14 88 176 96 195 131 387), lower := (rows 37 259 14 88 176 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 257 45 120 176 96 96 128 256) }] }

theorem u25692 : Upper (D 7) (R 7) [36,257,10,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25693 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 14 88 176 160 67 195 323), lower := (rows 37 259 14 88 176 160 64 128 256), losses := [] }

theorem u25693 : Upper (D 7) (R 7) [36,257,10,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25694 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 259 14 104 81 34 208 144 400), lower := (rows 37 259 14 104 81 34 64 128 256), losses := [] }

theorem u25694 : Upper (D 7) (R 7) [36,257,10,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25695 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 259 14 104 81 48 194 130 386), lower := (rows 37 259 14 104 81 48 64 128 256), losses := [] }

theorem u25695 : Upper (D 7) (R 7) [36,257,10,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25695 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25696 : Route 9 := (fun mask => (mask,id))

def c25696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25696 : Upper (D 7) (R 7) [36,257,10,96,65,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96,65,128] 13 (by decide) (choices 1) [2,16,128] r25696 c25696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9024
  · exact u9025
  · exact u9026

def b25697 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 14 104 82 33 208 144 400), lower := (rows 37 259 14 104 82 33 64 128 256), losses := [] }

theorem u25697 : Upper (D 7) (R 7) [36,257,10,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25698 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 259 14 104 82 48 193 129 385), lower := (rows 37 259 14 104 82 48 64 128 256), losses := [] }

theorem u25698 : Upper (D 7) (R 7) [36,257,10,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25698 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25699 : Route 9 := (fun mask => (mask,id))

def c25699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25699 : Upper (D 7) (R 7) [36,257,10,96,66,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96,66,128] 13 (by decide) (choices 1) [1,16,128] r25699 c25699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9027
  · exact u9028
  · exact u9029

def b25700 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 259 14 104 145 34 208 208 464), lower := (rows 37 259 14 104 145 34 64 128 256), losses := [] }

theorem u25700 : Upper (D 7) (R 7) [36,257,10,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25701 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 37 259 14 104 145 48 194 194 450), lower := (rows 37 259 14 104 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 9 16 48 70 134 262), good := (rows 492 462 462 104 184 48 64 128 256) }] }

theorem u25701 : Upper (D 7) (R 7) [36,257,10,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25701 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25702 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 37 259 14 104 145 96 210 146 402), lower := (rows 37 259 14 104 145 96 64 128 256), losses := [] }

theorem u25702 : Upper (D 7) (R 7) [36,257,10,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25703 : Route 9 := (fun mask => (mask,id))

def c25703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25703 : Upper (D 7) (R 7) [36,257,10,96,129,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96,129,128] 13 (by decide) (choices 1) [2,16] r25703 c25703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9030
  · exact u9031

def b25704 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 14 104 146 33 208 208 464), lower := (rows 37 259 14 104 146 33 64 128 256), losses := [] }

theorem u25704 : Upper (D 7) (R 7) [36,257,10,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25705 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,5),(3,1),(4,5)], upper := (rows 37 259 14 104 146 48 193 193 449), lower := (rows 37 259 14 104 146 48 64 128 256), losses := [] }

theorem u25705 : Upper (D 7) (R 7) [36,257,10,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25705 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25706 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 37 259 14 104 146 96 209 145 401), lower := (rows 37 259 14 104 146 96 64 128 256), losses := [] }

theorem u25706 : Upper (D 7) (R 7) [36,257,10,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25707 : Route 9 := (fun mask => (mask,id))

def c25707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25707 : Upper (D 7) (R 7) [36,257,10,96,130,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,96,130,128] 13 (by decide) (choices 1) [1,16] r25707 c25707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9032
  · exact u9033

def b25708 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 14 104 208 33 210 146 402), lower := (rows 37 259 14 104 208 33 64 128 256), losses := [] }

theorem u25708 : Upper (D 7) (R 7) [36,257,10,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25709 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 37 259 14 104 208 34 209 145 401), lower := (rows 37 259 14 104 208 34 64 128 256), losses := [] }

theorem u25709 : Upper (D 7) (R 7) [36,257,10,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25710 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 259 14 104 208 48 195 131 387), lower := (rows 37 259 14 104 208 48 64 128 256), losses := [] }

theorem u25710 : Upper (D 7) (R 7) [36,257,10,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25710 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25711 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 3 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 37 259 14 104 208 160 83 147 275), lower := (rows 37 259 14 104 208 160 64 128 256), losses := [] }

theorem u25711 : Upper (D 7) (R 7) [36,257,10,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25712 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 259 14 200 50 33 208 208 464), lower := (rows 37 259 14 200 50 33 64 128 256), losses := [] }

theorem u25712 : Upper (D 7) (R 7) [36,257,10,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25713 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 259 14 200 50 48 193 193 449), lower := (rows 37 259 14 200 50 48 64 128 256), losses := [] }

theorem u25713 : Upper (D 7) (R 7) [36,257,10,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25713 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25714 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 402, targets := 64 }], pairs := [(0,1),(1,6),(4,0),(4,6)], upper := (rows 37 259 14 200 50 96 209 145 401), lower := (rows 37 259 14 200 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 104 64 128 256), good := (rows 52 258 62 232 50 96 96 128 256) },{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 257 45 232 48 96 96 128 256) }] }

theorem u25714 : Upper (D 7) (R 7) [36,257,10,192,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25715 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 14 200 81 34 240 176 432), lower := (rows 37 259 14 200 81 34 64 128 256), losses := [] }

theorem u25715 : Upper (D 7) (R 7) [36,257,10,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25716 : Route 9 := (fun mask => (mask,id))

def c25716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25716 : Upper (D 7) (R 7) [36,257,10,192,65,16] 13 := by
  apply FastRouting.sound _ _ [36,257,10,192,65,16] 13 (by decide) (choices 1) [2,32,128] r25716 c25716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9034
  · exact u9035
  · exact u9036

def b25717 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(1,7),(4,7)], upper := (rows 37 259 14 200 81 160 114 178 306), lower := (rows 37 259 14 200 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 257 45 232 81 160 64 160 256) }] }

theorem u25717 : Upper (D 7) (R 7) [36,257,10,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25718 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(3,1)], upper := (rows 37 259 14 200 82 33 240 176 432), lower := (rows 37 259 14 200 82 33 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 39 80 144 272), good := (rows 37 289 45 200 504 33 64 128 256) }] }

theorem u25718 : Upper (D 7) (R 7) [36,257,10,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25719 : Route 9 := (fun mask => (mask,id))

def c25719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25719 : Upper (D 7) (R 7) [36,257,10,192,66,16] 13 := by
  apply FastRouting.sound _ _ [36,257,10,192,66,16] 13 (by decide) (choices 1) [1,32,128] r25719 c25719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9037
  · exact u9038
  · exact u9039

def b25720 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 259 14 200 82 160 113 177 305), lower := (rows 37 259 14 200 82 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 257 45 232 80 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 259 47 168 18 160 0 160 256) }] }

theorem u25720 : Upper (D 7) (R 7) [36,257,10,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25721 : Route 9 := (fun mask => (mask,id))

def c25721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25721 : Upper (D 7) (R 7) [36,257,10,192,96,1] 13 := by
  apply FastRouting.sound _ _ [36,257,10,192,96,1] 13 (by decide) (choices 1) [2,16,128] r25721 c25721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9040
  · exact u9041
  · exact u9042

def b25722 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 14 200 112 34 209 145 401), lower := (rows 37 259 14 200 112 34 64 128 256), losses := [] }

theorem u25722 : Upper (D 7) (R 7) [36,257,10,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25723 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 14 200 112 48 195 131 387), lower := (rows 37 259 14 200 112 48 64 128 256), losses := [] }

theorem u25723 : Upper (D 7) (R 7) [36,257,10,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25723 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25724 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 3, region := 48, targets := 3 }], pairs := [(1,7),(4,0),(4,1),(4,7)], upper := (rows 37 259 14 200 112 160 83 147 275), lower := (rows 37 259 14 200 112 160 64 128 256), losses := [] }

theorem u25724 : Upper (D 7) (R 7) [36,257,10,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25725 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 259 28 42 208 33 194 194 450), lower := (rows 37 259 28 42 208 33 64 128 256), losses := [] }

theorem u25725 : Upper (D 7) (R 7) [36,257,24,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25726 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 259 28 42 208 34 193 193 449), lower := (rows 37 259 28 42 208 34 64 128 256), losses := [] }

theorem u25726 : Upper (D 7) (R 7) [36,257,24,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25727 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 394, targets := 64 }], pairs := [(1,5),(1,6),(3,6),(4,5)], upper := (rows 37 259 28 42 208 96 195 131 387), lower := (rows 37 259 28 42 208 96 64 128 256), losses := [] }

theorem u25727 : Upper (D 7) (R 7) [36,257,24,34,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25728 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 37 259 28 73 82 34 224 160 416), lower := (rows 37 259 28 73 82 34 64 128 256), losses := [] }

theorem u25728 : Upper (D 7) (R 7) [36,257,24,65,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25729 : Route 9 := (fun mask => (mask,id))

def c25729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25729 : Upper (D 7) (R 7) [36,257,24,65,66,128] 13 := by
  apply FastRouting.sound _ _ [36,257,24,65,66,128] 13 (by decide) (choices 1) [2,32,128] r25729 c25729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9043
  · exact u9044
  · exact u9045

def b25730 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 200, targets := 2 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,6),(2,1),(3,1),(4,0)], upper := (rows 37 259 28 73 146 34 224 224 480), lower := (rows 37 259 28 73 146 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 11 16 32 97 161 289), good := (rows 493 457 28 457 156 488 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 50 0 128 256), good := (rows 37 291 61 9 178 34 0 128 256) }] }

theorem u25730 : Upper (D 7) (R 7) [36,257,24,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25731 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,1),(1,6),(4,0),(4,6)], upper := (rows 37 259 28 73 146 96 226 162 418), lower := (rows 37 259 28 73 146 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 104 64 128 256), good := (rows 37 257 61 105 144 96 96 128 256) }] }

theorem u25731 : Upper (D 7) (R 7) [36,257,24,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25732 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,1),(1,7),(3,7),(4,0)], upper := (rows 37 259 28 73 146 160 98 226 354), lower := (rows 37 259 28 73 146 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 257 61 73 176 160 64 160 256) }] }

theorem u25732 : Upper (D 7) (R 7) [36,257,24,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25733 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 1, region := 240, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,0)], upper := (rows 37 259 28 73 176 34 194 194 450), lower := (rows 37 259 28 73 176 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 51 34 98 162 290), good := (rows 500 498 28 92 496 498 64 128 256) }] }

theorem u25733 : Upper (D 7) (R 7) [36,257,24,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25734 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,5),(1,6),(3,5),(4,6)], upper := (rows 37 259 28 73 176 96 194 130 386), lower := (rows 37 259 28 73 176 96 64 128 256), losses := [] }

theorem u25734 : Upper (D 7) (R 7) [36,257,24,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25735 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 28 73 176 160 66 194 322), lower := (rows 37 259 28 73 176 160 64 128 256), losses := [] }

theorem u25735 : Upper (D 7) (R 7) [36,257,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25736 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 37 259 28 73 208 34 226 162 418), lower := (rows 37 259 28 73 208 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 51 34 98 162 290), good := (rows 500 498 28 92 208 498 64 128 256) }] }

theorem u25736 : Upper (D 7) (R 7) [36,257,24,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25737 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 37 259 28 73 208 160 98 162 290), lower := (rows 37 259 28 73 208 160 64 128 256), losses := [] }

theorem u25737 : Upper (D 7) (R 7) [36,257,24,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25738 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 28 74 146 33 224 224 480), lower := (rows 37 259 28 74 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 30 10 18 32 97 161 289), good := (rows 484 478 28 94 158 480 64 128 256) }] }

theorem u25738 : Upper (D 7) (R 7) [36,257,24,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25739 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,6),(2,6),(4,6)], upper := (rows 37 259 28 74 146 96 225 161 417), lower := (rows 37 259 28 74 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 3 12 8 19 32 0 129 257), good := (rows 439 403 28 30 146 32 0 128 256) }] }

theorem u25739 : Upper (D 7) (R 7) [36,257,24,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25739
end Delivery.IrregularNine14.P07
