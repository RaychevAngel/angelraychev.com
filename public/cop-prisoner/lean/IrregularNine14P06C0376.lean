import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0113
import IrregularNine14P06C0114

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r22560 : Route 9 := (fun mask => (mask,id))

def c22560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22560 : Upper (D 6) (R 6) [34,129,264,36,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,36,6,64] 13 (by decide) (choices 1) [1,16] r22560 c22560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6838
  · exact u6839

def b22561 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 44 81 34 84 212 340), lower := (rows 35 131 268 44 81 34 64 128 256), losses := [] }

theorem u22561 : Upper (D 6) (R 6) [34,129,264,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22562 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 268 44 81 36 82 210 338), lower := (rows 35 131 268 44 81 36 64 128 256), losses := [] }

theorem u22562 : Upper (D 6) (R 6) [34,129,264,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22563 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 268 44 81 48 70 198 326), lower := (rows 35 131 268 44 81 48 64 128 256), losses := [] }

theorem u22563 : Upper (D 6) (R 6) [34,129,264,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22563 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22564 : Route 9 := (fun mask => (mask,id))

def c22564 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22564 : Upper (D 6) (R 6) [34,129,264,36,65,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,36,65,64] 13 (by decide) (choices 1) [2,4,16] r22564 c22564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6840
  · exact u6841
  · exact u6842

def b22565 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 44 82 33 84 212 340), lower := (rows 35 131 268 44 82 33 64 128 256), losses := [] }

theorem u22565 : Upper (D 6) (R 6) [34,129,264,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22566 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 268 44 82 36 81 209 337), lower := (rows 35 131 268 44 82 36 64 128 256), losses := [] }

theorem u22566 : Upper (D 6) (R 6) [34,129,264,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22567 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 44 82 48 69 197 325), lower := (rows 35 131 268 44 82 48 64 128 256), losses := [] }

theorem u22567 : Upper (D 6) (R 6) [34,129,264,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22567 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22568 : Route 9 := (fun mask => (mask,id))

def c22568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22568 : Upper (D 6) (R 6) [34,129,264,36,66,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,36,66,64] 13 (by decide) (choices 1) [1,4,16] r22568 c22568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6843
  · exact u6844
  · exact u6845

def b22569 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 44 84 33 82 210 338), lower := (rows 35 131 268 44 84 33 64 128 256), losses := [] }

theorem u22569 : Upper (D 6) (R 6) [34,129,264,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22570 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 44 84 34 81 209 337), lower := (rows 35 131 268 44 84 34 64 128 256), losses := [] }

theorem u22570 : Upper (D 6) (R 6) [34,129,264,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22571 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 268 44 84 48 67 195 323), lower := (rows 35 131 268 44 84 48 64 128 256), losses := [] }

theorem u22571 : Upper (D 6) (R 6) [34,129,264,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22571 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22572 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 40, targets := 3 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 131 268 44 84 96 83 147 275), lower := (rows 35 131 268 44 84 96 64 128 256), losses := [] }

theorem u22572 : Upper (D 6) (R 6) [34,129,264,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22573 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 56 21 34 68 196 324), lower := (rows 35 131 268 56 21 34 64 128 256), losses := [] }

theorem u22573 : Upper (D 6) (R 6) [34,129,264,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22574 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 268 56 21 36 66 194 322), lower := (rows 35 131 268 56 21 36 64 128 256), losses := [] }

theorem u22574 : Upper (D 6) (R 6) [34,129,264,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22575 : Route 9 := (fun mask => (mask,id))

def c22575 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22575 : Upper (D 6) (R 6) [34,129,264,48,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48,5,64] 13 (by decide) (choices 1) [2,4] r22575 c22575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6846
  · exact u6847

def b22576 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 131 268 56 22 33 68 196 324), lower := (rows 35 131 268 56 22 33 64 128 256), losses := [] }

theorem u22576 : Upper (D 6) (R 6) [34,129,264,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22577 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 194, targets := 36 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,2),(1,5),(3,0)], upper := (rows 35 131 268 56 22 36 65 193 321), lower := (rows 35 131 268 56 22 36 64 128 256), losses := [] }

theorem u22577 : Upper (D 6) (R 6) [34,129,264,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22578 : Route 9 := (fun mask => (mask,id))

def c22578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22578 : Upper (D 6) (R 6) [34,129,264,48,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48,6,64] 13 (by decide) (choices 1) [1,4] r22578 c22578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6848
  · exact u6849

def b22579 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 56 81 34 68 196 324), lower := (rows 35 131 268 56 81 34 64 128 256), losses := [] }

theorem u22579 : Upper (D 6) (R 6) [34,129,264,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22580 : Route 9 := (fun mask => (mask,id))

def c22580 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22580 : Upper (D 6) (R 6) [34,129,264,48,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48,65,4] 13 (by decide) (choices 1) [2,4] r22580 c22580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6850
  · exact u6851

def b22581 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 56 81 96 70 134 262), lower := (rows 35 131 268 56 81 96 64 128 256), losses := [] }

theorem u22581 : Upper (D 6) (R 6) [34,129,264,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22582 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 131 268 56 82 33 68 196 324), lower := (rows 35 131 268 56 82 33 64 128 256), losses := [] }

theorem u22582 : Upper (D 6) (R 6) [34,129,264,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22583 : Route 9 := (fun mask => (mask,id))

def c22583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22583 : Upper (D 6) (R 6) [34,129,264,48,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48,66,4] 13 (by decide) (choices 1) [1,4] r22583 c22583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6852
  · exact u6853

def b22584 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 56 82 96 69 133 261), lower := (rows 35 131 268 56 82 96 64 128 256), losses := [] }

theorem u22584 : Upper (D 6) (R 6) [34,129,264,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22585 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 56 84 33 70 198 326), lower := (rows 35 131 268 56 84 33 64 128 256), losses := [] }

theorem u22585 : Upper (D 6) (R 6) [34,129,264,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22586 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 56 84 34 69 197 325), lower := (rows 35 131 268 56 84 34 64 128 256), losses := [] }

theorem u22586 : Upper (D 6) (R 6) [34,129,264,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22587 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 268 56 84 36 67 195 323), lower := (rows 35 131 268 56 84 36 64 128 256), losses := [] }

theorem u22587 : Upper (D 6) (R 6) [34,129,264,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22588 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 131 268 56 84 96 71 135 263), lower := (rows 35 131 268 56 84 96 64 128 256), losses := [] }

theorem u22588 : Upper (D 6) (R 6) [34,129,264,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22589 : Route 9 := (fun mask => (mask,id))

def c22589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22589 : Upper (D 6) (R 6) [34,129,264,65,6,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,6,4] 13 (by decide) (choices 1) [16,32] r22589 c22589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6854
  · exact u6855

def b22590 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 73 22 48 100 228 356), lower := (rows 35 131 268 73 22 48 64 128 256), losses := [] }

theorem u22590 : Upper (D 6) (R 6) [34,129,264,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22590 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22591 : Route 9 := (fun mask => (mask,id))

def c22591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22591 : Upper (D 6) (R 6) [34,129,264,65,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,6,64] 13 (by decide) (choices 1) [4,16,32] r22591 c22591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6856
  · exact u6857
  · exact u6858

def b22592 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 73 52 34 84 212 340), lower := (rows 35 131 268 73 52 34 64 128 256), losses := [] }

theorem u22592 : Upper (D 6) (R 6) [34,129,264,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22593 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 268 73 52 36 82 210 338), lower := (rows 35 131 268 73 52 36 64 128 256), losses := [] }

theorem u22593 : Upper (D 6) (R 6) [34,129,264,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22594 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 73 52 48 70 198 326), lower := (rows 35 131 268 73 52 48 64 128 256), losses := [] }

theorem u22594 : Upper (D 6) (R 6) [34,129,264,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22594 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22595 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 35 131 268 73 52 96 86 150 278), lower := (rows 35 131 268 73 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 104 64 128 256), good := (rows 34 130 316 104 52 96 96 128 256) }] }

theorem u22595 : Upper (D 6) (R 6) [34,129,264,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22596 : Route 9 := (fun mask => (mask,id))

def c22596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22596 : Upper (D 6) (R 6) [34,129,264,65,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,66,4] 13 (by decide) (choices 1) [4,16,32] r22596 c22596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6859
  · exact u6860
  · exact u6861

def b22597 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 268 73 82 48 100 164 292), lower := (rows 35 131 268 73 82 48 64 128 256), losses := [] }

theorem u22597 : Upper (D 6) (R 6) [34,129,264,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22597 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22598 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 73 84 34 116 180 308), lower := (rows 35 131 268 73 84 34 64 128 256), losses := [] }

theorem u22598 : Upper (D 6) (R 6) [34,129,264,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22599 : Route 9 := (fun mask => (mask,id))

def c22599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22599 : Upper (D 6) (R 6) [34,129,264,65,68,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,68,4] 13 (by decide) (choices 1) [2,16,32] r22599 c22599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6862
  · exact u6863
  · exact u6864

def b22600 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 73 84 48 102 166 294), lower := (rows 35 131 268 73 84 48 64 128 256), losses := [] }

theorem u22600 : Upper (D 6) (R 6) [34,129,264,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22600 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22601 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 73 112 34 84 148 276), lower := (rows 35 131 268 73 112 34 64 128 256), losses := [] }

theorem u22601 : Upper (D 6) (R 6) [34,129,264,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22602 : Route 9 := (fun mask => (mask,id))

def c22602 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22602 : Upper (D 6) (R 6) [34,129,264,65,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65,96,4] 13 (by decide) (choices 1) [2,4,16] r22602 c22602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6865
  · exact u6866
  · exact u6867

def b22603 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 73 112 48 70 134 262), lower := (rows 35 131 268 73 112 48 64 128 256), losses := [] }

theorem u22603 : Upper (D 6) (R 6) [34,129,264,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22603 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22604 : Route 9 := (fun mask => (mask,id))

def c22604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22604 : Upper (D 6) (R 6) [34,129,264,66,5,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,5,4] 13 (by decide) (choices 1) [16,32] r22604 c22604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6868
  · exact u6869

def b22605 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 268 74 21 48 100 228 356), lower := (rows 35 131 268 74 21 48 64 128 256), losses := [] }

theorem u22605 : Upper (D 6) (R 6) [34,129,264,66,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22605 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22606 : Route 9 := (fun mask => (mask,id))

def c22606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22606 : Upper (D 6) (R 6) [34,129,264,66,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,5,64] 13 (by decide) (choices 1) [4,16,32] r22606 c22606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6870
  · exact u6871
  · exact u6872

def b22607 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 74 52 33 84 212 340), lower := (rows 35 131 268 74 52 33 64 128 256), losses := [] }

theorem u22607 : Upper (D 6) (R 6) [34,129,264,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22608 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 268 74 52 36 81 209 337), lower := (rows 35 131 268 74 52 36 64 128 256), losses := [] }

theorem u22608 : Upper (D 6) (R 6) [34,129,264,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22609 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 74 52 48 69 197 325), lower := (rows 35 131 268 74 52 48 64 128 256), losses := [] }

theorem u22609 : Upper (D 6) (R 6) [34,129,264,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22609 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22610 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 131, targets := 64 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 131 268 74 52 96 85 149 277), lower := (rows 35 131 268 74 52 96 64 128 256), losses := [] }

theorem u22610 : Upper (D 6) (R 6) [34,129,264,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22611 : Route 9 := (fun mask => (mask,id))

def c22611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22611 : Upper (D 6) (R 6) [34,129,264,66,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,65,4] 13 (by decide) (choices 1) [4,16,32] r22611 c22611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6873
  · exact u6874
  · exact u6875

def b22612 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 268 74 81 48 100 164 292), lower := (rows 35 131 268 74 81 48 64 128 256), losses := [] }

theorem u22612 : Upper (D 6) (R 6) [34,129,264,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22612 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22613 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 74 84 33 116 180 308), lower := (rows 35 131 268 74 84 33 64 128 256), losses := [] }

theorem u22613 : Upper (D 6) (R 6) [34,129,264,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22614 : Route 9 := (fun mask => (mask,id))

def c22614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22614 : Upper (D 6) (R 6) [34,129,264,66,68,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,68,4] 13 (by decide) (choices 1) [1,16,32] r22614 c22614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6876
  · exact u6877
  · exact u6878

def b22615 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 268 74 84 48 101 165 293), lower := (rows 35 131 268 74 84 48 64 128 256), losses := [] }

theorem u22615 : Upper (D 6) (R 6) [34,129,264,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22615 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22616 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 74 112 33 84 148 276), lower := (rows 35 131 268 74 112 33 64 128 256), losses := [] }

theorem u22616 : Upper (D 6) (R 6) [34,129,264,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22617 : Route 9 := (fun mask => (mask,id))

def c22617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22617 : Upper (D 6) (R 6) [34,129,264,66,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66,96,4] 13 (by decide) (choices 1) [1,4,16] r22617 c22617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6879
  · exact u6880
  · exact u6881

def b22618 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 268 74 112 48 69 133 261), lower := (rows 35 131 268 74 112 48 64 128 256), losses := [] }

theorem u22618 : Upper (D 6) (R 6) [34,129,264,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22618 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22619 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 268 76 21 34 112 240 368), lower := (rows 35 131 268 76 21 34 64 128 256), losses := [] }

theorem u22619 : Upper (D 6) (R 6) [34,129,264,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22619
end Delivery.IrregularNine14.P06
