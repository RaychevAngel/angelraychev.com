import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0132
import IrregularNine14P06C0133

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r25680 : Route 9 := (fun mask => (mask,id))

def c25680 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25680 : Upper (D 6) (R 6) [40,80,129,320,3,4] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,3,4] 13 (by decide) (choices 1) [2,4,32] r25680 c25680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7969
  · exact u7970
  · exact u7971

def b25681 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 133 328 22 33 102 166 294), lower := (rows 41 82 133 328 22 33 64 128 256), losses := [] }

theorem u25681 : Upper (D 6) (R 6) [40,80,129,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25682 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 328 22 34 101 165 293), lower := (rows 41 82 133 328 22 34 64 128 256), losses := [] }

theorem u25682 : Upper (D 6) (R 6) [40,80,129,320,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25683 : Route 9 := (fun mask => (mask,id))

def c25683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25683 : Upper (D 6) (R 6) [40,80,129,320,6,4] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,6,4] 13 (by decide) (choices 1) [1,2,32] r25683 c25683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7972
  · exact u7973
  · exact u7974

def b25684 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 133 328 50 33 70 134 262), lower := (rows 41 82 133 328 50 33 64 128 256), losses := [] }

theorem u25684 : Upper (D 6) (R 6) [40,80,129,320,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25685 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 82 133 328 50 34 69 133 261), lower := (rows 41 82 133 328 50 34 64 128 256), losses := [] }

theorem u25685 : Upper (D 6) (R 6) [40,80,129,320,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25686 : Route 9 := (fun mask => (mask,id))

def c25686 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25686 : Upper (D 6) (R 6) [40,80,129,320,34,4] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,34,4] 13 (by decide) (choices 1) [1,2,4] r25686 c25686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7975
  · exact u7976
  · exact u7977

def b25687 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 82 133 328 52 33 70 134 262), lower := (rows 41 82 133 328 52 33 64 128 256), losses := [] }

theorem u25687 : Upper (D 6) (R 6) [40,80,129,320,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25688 : Route 9 := (fun mask => (mask,id))

def c25688 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25688 : Upper (D 6) (R 6) [40,80,129,320,36,2] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,36,2] 13 (by decide) (choices 1) [1,2,4] r25688 c25688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7978
  · exact u7979
  · exact u7980

def b25689 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 82 133 328 52 36 67 131 259), lower := (rows 41 82 133 328 52 36 64 128 256), losses := [] }

theorem u25689 : Upper (D 6) (R 6) [40,80,129,320,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25690 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 164 11 22 33 324 452 324), lower := (rows 41 82 164 11 22 33 64 128 256), losses := [] }

theorem u25690 : Upper (D 6) (R 6) [40,80,160,3,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25691 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 11 22 36 321 449 321), lower := (rows 41 82 164 11 22 36 64 128 256), losses := [] }

theorem u25691 : Upper (D 6) (R 6) [40,80,160,3,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25692 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 3, region := 485, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 41 82 164 11 22 96 325 389 261), lower := (rows 41 82 164 11 22 96 64 128 256), losses := [] }

theorem u25692 : Upper (D 6) (R 6) [40,80,160,3,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25693 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 485, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 82 164 11 22 288 69 197 325), lower := (rows 41 82 164 11 22 288 64 128 256), losses := [] }

theorem u25693 : Upper (D 6) (R 6) [40,80,160,3,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25693 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25694 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 164 11 273 34 68 196 324), lower := (rows 41 82 164 11 273 34 64 128 256), losses := [] }

theorem u25694 : Upper (D 6) (R 6) [40,80,160,3,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25695 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 11 273 36 70 198 326), lower := (rows 41 82 164 11 273 36 64 128 256), losses := [] }

theorem u25695 : Upper (D 6) (R 6) [40,80,160,3,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25696 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 82 164 11 273 96 70 134 262), lower := (rows 41 82 164 11 273 96 64 128 256), losses := [] }

theorem u25696 : Upper (D 6) (R 6) [40,80,160,3,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25697 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 164 11 274 33 68 196 324), lower := (rows 41 82 164 11 274 33 64 128 256), losses := [] }

theorem u25697 : Upper (D 6) (R 6) [40,80,160,3,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25698 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 11 274 36 69 197 325), lower := (rows 41 82 164 11 274 36 64 128 256), losses := [] }

theorem u25698 : Upper (D 6) (R 6) [40,80,160,3,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25699 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 41 82 164 11 274 96 69 133 261), lower := (rows 41 82 164 11 274 96 64 128 256), losses := [] }

theorem u25699 : Upper (D 6) (R 6) [40,80,160,3,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25700 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 164 11 276 33 70 198 326), lower := (rows 41 82 164 11 276 33 64 128 256), losses := [] }

theorem u25700 : Upper (D 6) (R 6) [40,80,160,3,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25701 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 164 11 276 34 69 197 325), lower := (rows 41 82 164 11 276 34 64 128 256), losses := [] }

theorem u25701 : Upper (D 6) (R 6) [40,80,160,3,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25702 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 11 276 36 67 195 323), lower := (rows 41 82 164 11 276 36 64 128 256), losses := [] }

theorem u25702 : Upper (D 6) (R 6) [40,80,160,3,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25703 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 41, targets := 4 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 41 82 164 11 276 96 71 135 263), lower := (rows 41 82 164 11 276 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 98 64 128 256), good := (rows 41 112 164 41 276 96 96 128 256) }] }

theorem u25703 : Upper (D 6) (R 6) [40,80,160,3,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25704 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 82 164 14 19 33 324 452 324), lower := (rows 41 82 164 14 19 33 64 128 256), losses := [] }

theorem u25704 : Upper (D 6) (R 6) [40,80,160,6,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25705 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 164 14 19 36 321 449 321), lower := (rows 41 82 164 14 19 36 64 128 256), losses := [] }

theorem u25705 : Upper (D 6) (R 6) [40,80,160,6,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25706 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 485, targets := 2 },{ cop := 0, region := 388, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 41 82 164 14 19 96 325 389 261), lower := (rows 41 82 164 14 19 96 64 128 256), losses := [] }

theorem u25706 : Upper (D 6) (R 6) [40,80,160,6,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25707 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 485, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 82 164 14 19 288 69 197 325), lower := (rows 41 82 164 14 19 288 64 128 256), losses := [] }

theorem u25707 : Upper (D 6) (R 6) [40,80,160,6,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25707 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25708 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 164 14 273 33 70 198 326), lower := (rows 41 82 164 14 273 33 64 128 256), losses := [] }

theorem u25708 : Upper (D 6) (R 6) [40,80,160,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25709 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 82 164 14 273 34 69 197 325), lower := (rows 41 82 164 14 273 34 64 128 256), losses := [] }

theorem u25709 : Upper (D 6) (R 6) [40,80,160,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25710 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 164 14 273 36 67 195 323), lower := (rows 41 82 164 14 273 36 64 128 256), losses := [] }

theorem u25710 : Upper (D 6) (R 6) [40,80,160,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25711 : Route 9 := (fun mask => (mask,id))

def c25711 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25711 : Upper (D 6) (R 6) [40,80,160,6,257,64] 13 := by
  apply FastRouting.sound _ _ [40,80,160,6,257,64] 13 (by decide) (choices 1) [1,2,4] r25711 c25711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7981
  · exact u7982
  · exact u7983

def b25712 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 82 164 14 274 33 69 197 325), lower := (rows 41 82 164 14 274 33 64 128 256), losses := [] }

theorem u25712 : Upper (D 6) (R 6) [40,80,160,6,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25713 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 164 14 274 36 65 193 321), lower := (rows 41 82 164 14 274 36 64 128 256), losses := [] }

theorem u25713 : Upper (D 6) (R 6) [40,80,160,6,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25714 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 41 82 164 14 274 96 69 133 261), lower := (rows 41 82 164 14 274 96 64 128 256), losses := [] }

theorem u25714 : Upper (D 6) (R 6) [40,80,160,6,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25715 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 164 14 276 33 67 195 323), lower := (rows 41 82 164 14 276 33 64 128 256), losses := [] }

theorem u25715 : Upper (D 6) (R 6) [40,80,160,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25716 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 82 164 14 276 34 65 193 321), lower := (rows 41 82 164 14 276 34 64 128 256), losses := [] }

theorem u25716 : Upper (D 6) (R 6) [40,80,160,6,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25717 : Route 9 := (fun mask => (mask,id))

def c25717 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25717 : Upper (D 6) (R 6) [40,80,160,6,260,64] 13 := by
  apply FastRouting.sound _ _ [40,80,160,6,260,64] 13 (by decide) (choices 1) [1,2] r25717 c25717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7984
  · exact u7985

def b25718 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 82 164 73 22 33 326 390 262), lower := (rows 41 82 164 73 22 33 64 128 256), losses := [] }

theorem u25718 : Upper (D 6) (R 6) [40,80,160,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25719 : PairBound 9 := { available := 261, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 164 73 22 34 325 389 261), lower := (rows 41 82 164 73 22 34 64 128 256), losses := [] }

theorem u25719 : Upper (D 6) (R 6) [40,80,160,65,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25720 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 73 22 36 323 387 259), lower := (rows 41 82 164 73 22 36 64 128 256), losses := [] }

theorem u25720 : Upper (D 6) (R 6) [40,80,160,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25721 : Route 9 := (fun mask => (mask,id))

def c25721 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25721 : Upper (D 6) (R 6) [40,80,160,65,6,256] 13 := by
  apply FastRouting.sound _ _ [40,80,160,65,6,256] 13 (by decide) (choices 1) [1,2,4] r25721 c25721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7986
  · exact u7987
  · exact u7988

def b25722 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 82 164 73 274 33 70 134 262), lower := (rows 41 82 164 73 274 33 64 128 256), losses := [] }

theorem u25722 : Upper (D 6) (R 6) [40,80,160,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25723 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 205, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 164 73 274 34 69 133 261), lower := (rows 41 82 164 73 274 34 64 128 256), losses := [] }

theorem u25723 : Upper (D 6) (R 6) [40,80,160,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25724 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 73 274 36 71 135 263), lower := (rows 41 82 164 73 274 36 64 128 256), losses := [] }

theorem u25724 : Upper (D 6) (R 6) [40,80,160,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25725 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 82 164 73 276 33 70 134 262), lower := (rows 41 82 164 73 276 33 64 128 256), losses := [] }

theorem u25725 : Upper (D 6) (R 6) [40,80,160,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25726 : Route 9 := (fun mask => (mask,id))

def c25726 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25726 : Upper (D 6) (R 6) [40,80,160,65,260,2] 13 := by
  apply FastRouting.sound _ _ [40,80,160,65,260,2] 13 (by decide) (choices 1) [1,2,4] r25726 c25726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7989
  · exact u7990
  · exact u7991

def b25727 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 73 276 36 67 131 259), lower := (rows 41 82 164 73 276 36 64 128 256), losses := [] }

theorem u25727 : Upper (D 6) (R 6) [40,80,160,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25728 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 164 76 19 33 326 390 262), lower := (rows 41 82 164 76 19 33 64 128 256), losses := [] }

theorem u25728 : Upper (D 6) (R 6) [40,80,160,68,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25729 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 164 76 19 34 325 389 261), lower := (rows 41 82 164 76 19 34 64 128 256), losses := [] }

theorem u25729 : Upper (D 6) (R 6) [40,80,160,68,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25730 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 164 76 19 36 323 387 259), lower := (rows 41 82 164 76 19 36 64 128 256), losses := [] }

theorem u25730 : Upper (D 6) (R 6) [40,80,160,68,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25731 : Route 9 := (fun mask => (mask,id))

def c25731 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25731 : Upper (D 6) (R 6) [40,80,160,68,3,256] 13 := by
  apply FastRouting.sound _ _ [40,80,160,68,3,256] 13 (by decide) (choices 1) [1,2,4] r25731 c25731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7992
  · exact u7993
  · exact u7994

def b25732 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 164 76 273 33 70 134 262), lower := (rows 41 82 164 76 273 33 64 128 256), losses := [] }

theorem u25732 : Upper (D 6) (R 6) [40,80,160,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25733 : Route 9 := (fun mask => (mask,id))

def c25733 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25733 : Upper (D 6) (R 6) [40,80,160,68,257,2] 13 := by
  apply FastRouting.sound _ _ [40,80,160,68,257,2] 13 (by decide) (choices 1) [1,2,4] r25733 c25733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7995
  · exact u7996
  · exact u7997

def b25734 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 164 76 273 36 67 131 259), lower := (rows 41 82 164 76 273 36 64 128 256), losses := [] }

theorem u25734 : Upper (D 6) (R 6) [40,80,160,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25735 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 164 76 274 33 71 135 263), lower := (rows 41 82 164 76 274 33 64 128 256), losses := [] }

theorem u25735 : Upper (D 6) (R 6) [40,80,160,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25736 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 205, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 164 76 274 34 69 133 261), lower := (rows 41 82 164 76 274 34 64 128 256), losses := [] }

theorem u25736 : Upper (D 6) (R 6) [40,80,160,68,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25737 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 164 76 274 36 67 131 259), lower := (rows 41 82 164 76 274 36 64 128 256), losses := [] }

theorem u25737 : Upper (D 6) (R 6) [40,80,160,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25738 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 164 76 276 33 67 131 259), lower := (rows 41 82 164 76 276 33 64 128 256), losses := [] }

theorem u25738 : Upper (D 6) (R 6) [40,80,160,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25739 : Route 9 := (fun mask => (mask,id))

def c25739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25739 : Upper (D 6) (R 6) [40,80,160,68,260,2] 13 := by
  apply FastRouting.sound _ _ [40,80,160,68,260,2] 13 (by decide) (choices 1) [1,2] r25739 c25739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7998
  · exact u7999

#print axioms u25739
end Delivery.IrregularNine14.P06
