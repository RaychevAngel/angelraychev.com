import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0133

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25740 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 164 265 19 34 68 196 324), lower := (rows 41 82 164 265 19 34 64 128 256), losses := [] }

theorem u25740 : Upper (D 6) (R 6) [40,80,160,257,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25741 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 265 19 36 70 198 326), lower := (rows 41 82 164 265 19 36 64 128 256), losses := [] }

theorem u25741 : Upper (D 6) (R 6) [40,80,160,257,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25742 : Route 9 := (fun mask => (mask,id))

def c25742 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25742 : Upper (D 6) (R 6) [40,80,160,257,3,64] 13 := by
  apply FastRouting.sound _ _ [40,80,160,257,3,64] 13 (by decide) (choices 1) [2,4] r25742 c25742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8000
  · exact u8001

def b25743 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 164 265 22 33 70 198 326), lower := (rows 41 82 164 265 22 33 64 128 256), losses := [] }

theorem u25743 : Upper (D 6) (R 6) [40,80,160,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25744 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 164 265 22 34 69 197 325), lower := (rows 41 82 164 265 22 34 64 128 256), losses := [] }

theorem u25744 : Upper (D 6) (R 6) [40,80,160,257,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25745 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 265 22 36 67 195 323), lower := (rows 41 82 164 265 22 36 64 128 256), losses := [] }

theorem u25745 : Upper (D 6) (R 6) [40,80,160,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25746 : Route 9 := (fun mask => (mask,id))

def c25746 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25746 : Upper (D 6) (R 6) [40,80,160,257,6,64] 13 := by
  apply FastRouting.sound _ _ [40,80,160,257,6,64] 13 (by decide) (choices 1) [1,2,4] r25746 c25746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8002
  · exact u8003
  · exact u8004

def b25747 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 82 164 266 19 33 68 196 324), lower := (rows 41 82 164 266 19 33 64 128 256), losses := [] }

theorem u25747 : Upper (D 6) (R 6) [40,80,160,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25748 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 266 19 36 69 197 325), lower := (rows 41 82 164 266 19 36 64 128 256), losses := [] }

theorem u25748 : Upper (D 6) (R 6) [40,80,160,258,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25749 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 41 82 164 266 19 96 69 133 261), lower := (rows 41 82 164 266 19 96 64 128 256), losses := [] }

theorem u25749 : Upper (D 6) (R 6) [40,80,160,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25750 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 82 164 266 21 33 70 198 326), lower := (rows 41 82 164 266 21 33 64 128 256), losses := [] }

theorem u25750 : Upper (D 6) (R 6) [40,80,160,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25751 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 82 164 266 21 34 69 197 325), lower := (rows 41 82 164 266 21 34 64 128 256), losses := [] }

theorem u25751 : Upper (D 6) (R 6) [40,80,160,258,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25752 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 41 82 164 266 21 36 67 195 323), lower := (rows 41 82 164 266 21 36 64 128 256), losses := [] }

theorem u25752 : Upper (D 6) (R 6) [40,80,160,258,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25753 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 330, targets := 32 }], pairs := [(0,1),(1,5),(3,5)], upper := (rows 41 82 164 266 21 96 71 135 263), lower := (rows 41 82 164 266 21 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 98 64 128 256), good := (rows 41 112 164 297 21 96 96 128 256) }] }

theorem u25753 : Upper (D 6) (R 6) [40,80,160,258,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25754 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 82 164 266 22 33 69 197 325), lower := (rows 41 82 164 266 22 33 64 128 256), losses := [] }

theorem u25754 : Upper (D 6) (R 6) [40,80,160,258,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25755 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 266 22 36 65 193 321), lower := (rows 41 82 164 266 22 36 64 128 256), losses := [] }

theorem u25755 : Upper (D 6) (R 6) [40,80,160,258,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25756 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 41 82 164 266 22 96 69 133 261), lower := (rows 41 82 164 266 22 96 64 128 256), losses := [] }

theorem u25756 : Upper (D 6) (R 6) [40,80,160,258,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25757 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 164 268 19 33 70 198 326), lower := (rows 41 82 164 268 19 33 64 128 256), losses := [] }

theorem u25757 : Upper (D 6) (R 6) [40,80,160,260,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25758 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 164 268 19 34 69 197 325), lower := (rows 41 82 164 268 19 34 64 128 256), losses := [] }

theorem u25758 : Upper (D 6) (R 6) [40,80,160,260,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25759 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 82, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 164 268 19 36 67 195 323), lower := (rows 41 82 164 268 19 36 64 128 256), losses := [] }

theorem u25759 : Upper (D 6) (R 6) [40,80,160,260,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25760 : Route 9 := (fun mask => (mask,id))

def c25760 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25760 : Upper (D 6) (R 6) [40,80,160,260,3,64] 13 := by
  apply FastRouting.sound _ _ [40,80,160,260,3,64] 13 (by decide) (choices 1) [1,2,4] r25760 c25760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8005
  · exact u8006
  · exact u8007

def b25761 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 164 268 22 33 67 195 323), lower := (rows 41 82 164 268 22 33 64 128 256), losses := [] }

theorem u25761 : Upper (D 6) (R 6) [40,80,160,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25762 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 164 268 22 34 65 193 321), lower := (rows 41 82 164 268 22 34 64 128 256), losses := [] }

theorem u25762 : Upper (D 6) (R 6) [40,80,160,260,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25763 : Route 9 := (fun mask => (mask,id))

def c25763 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25763 : Upper (D 6) (R 6) [40,80,160,260,6,64] 13 := by
  apply FastRouting.sound _ _ [40,80,160,260,6,64] 13 (by decide) (choices 1) [1,2] r25763 c25763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8008
  · exact u8009

def b25764 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 164 328 19 33 70 134 262), lower := (rows 41 82 164 328 19 33 64 128 256), losses := [] }

theorem u25764 : Upper (D 6) (R 6) [40,80,160,320,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25765 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 164 328 19 34 69 133 261), lower := (rows 41 82 164 328 19 34 64 128 256), losses := [] }

theorem u25765 : Upper (D 6) (R 6) [40,80,160,320,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25766 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 328 19 36 71 135 263), lower := (rows 41 82 164 328 19 36 64 128 256), losses := [] }

theorem u25766 : Upper (D 6) (R 6) [40,80,160,320,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25767 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 82 164 328 21 33 70 134 262), lower := (rows 41 82 164 328 21 33 64 128 256), losses := [] }

theorem u25767 : Upper (D 6) (R 6) [40,80,160,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25768 : Route 9 := (fun mask => (mask,id))

def c25768 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25768 : Upper (D 6) (R 6) [40,80,160,320,5,2] 13 := by
  apply FastRouting.sound _ _ [40,80,160,320,5,2] 13 (by decide) (choices 1) [1,2,4] r25768 c25768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8010
  · exact u8011
  · exact u8012

def b25769 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 41 82 164 328 21 36 67 131 259), lower := (rows 41 82 164 328 21 36 64 128 256), losses := [] }

theorem u25769 : Upper (D 6) (R 6) [40,80,160,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25770 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 164 328 22 33 71 135 263), lower := (rows 41 82 164 328 22 33 64 128 256), losses := [] }

theorem u25770 : Upper (D 6) (R 6) [40,80,160,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25771 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 164 328 22 34 69 133 261), lower := (rows 41 82 164 328 22 34 64 128 256), losses := [] }

theorem u25771 : Upper (D 6) (R 6) [40,80,160,320,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25772 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 82 164 328 22 36 67 131 259), lower := (rows 41 82 164 328 22 36 64 128 256), losses := [] }

theorem u25772 : Upper (D 6) (R 6) [40,80,160,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25773 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 388 11 21 34 100 228 356), lower := (rows 41 82 388 11 21 34 64 128 256), losses := [] }

theorem u25773 : Upper (D 6) (R 6) [40,80,384,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25774 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(0,6),(1,0),(2,0)], upper := (rows 41 82 388 11 21 36 98 226 354), lower := (rows 41 82 388 11 21 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 10 16 52 0 128 256), good := (rows 41 59 420 11 53 36 0 128 256) }] }

theorem u25774 : Upper (D 6) (R 6) [40,80,384,3,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25775 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 82 388 11 21 96 102 166 294), lower := (rows 41 82 388 11 21 96 64 128 256), losses := [] }

theorem u25775 : Upper (D 6) (R 6) [40,80,384,3,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25776 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 388 11 22 33 100 228 356), lower := (rows 41 82 388 11 22 33 64 128 256), losses := [] }

theorem u25776 : Upper (D 6) (R 6) [40,80,384,3,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25777 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 485, targets := 2 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 388 11 22 36 97 225 353), lower := (rows 41 82 388 11 22 36 64 128 256), losses := [] }

theorem u25777 : Upper (D 6) (R 6) [40,80,384,3,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25778 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 3, region := 485, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 41 82 388 11 22 96 101 165 293), lower := (rows 41 82 388 11 22 96 64 128 256), losses := [] }

theorem u25778 : Upper (D 6) (R 6) [40,80,384,3,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25779 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 388 11 52 33 70 198 326), lower := (rows 41 82 388 11 52 33 64 128 256), losses := [] }

theorem u25779 : Upper (D 6) (R 6) [40,80,384,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25780 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 388 11 52 34 69 197 325), lower := (rows 41 82 388 11 52 34 64 128 256), losses := [] }

theorem u25780 : Upper (D 6) (R 6) [40,80,384,3,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25781 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 82 388 11 52 36 67 195 323), lower := (rows 41 82 388 11 52 36 64 128 256), losses := [] }

theorem u25781 : Upper (D 6) (R 6) [40,80,384,3,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25782 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 3, region := 388, targets := 32 }], pairs := [(0,2),(2,5),(3,2)], upper := (rows 41 82 388 11 52 96 71 135 263), lower := (rows 41 82 388 11 52 96 64 128 256), losses := [] }

theorem u25782 : Upper (D 6) (R 6) [40,80,384,3,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25783 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 388 13 22 33 98 226 354), lower := (rows 41 82 388 13 22 33 64 128 256), losses := [] }

theorem u25783 : Upper (D 6) (R 6) [40,80,384,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25784 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 388 13 22 34 97 225 353), lower := (rows 41 82 388 13 22 34 64 128 256), losses := [] }

theorem u25784 : Upper (D 6) (R 6) [40,80,384,5,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m25785_1 : Upper (D 6) (R 6) [40,80,384,5,6,64,1] 13 :=
  permutation_upper _ _ _ [40,80,384,5,6,2,32] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8014

theorem m25785_2 : Upper (D 6) (R 6) [40,80,384,5,6,64,2] 13 :=
  permutation_upper _ _ _ [40,80,384,5,6,1,32] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8013

def r25785 : Route 9 := (fun mask => (mask,id))

def c25785 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25785 : Upper (D 6) (R 6) [40,80,384,5,6,64] 13 := by
  apply FastRouting.sound _ _ [40,80,384,5,6,64] 13 (by decide) (choices 1) [1,2,32] r25785 c25785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m25785_1
  · exact m25785_2
  · exact u8015

def b25786 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 388 13 50 33 70 198 326), lower := (rows 41 82 388 13 50 33 64 128 256), losses := [] }

theorem u25786 : Upper (D 6) (R 6) [40,80,384,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25787 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 82 388 13 50 34 69 197 325), lower := (rows 41 82 388 13 50 34 64 128 256), losses := [] }

theorem u25787 : Upper (D 6) (R 6) [40,80,384,5,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25788 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 388 13 50 36 67 195 323), lower := (rows 41 82 388 13 50 36 64 128 256), losses := [] }

theorem u25788 : Upper (D 6) (R 6) [40,80,384,5,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25789 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 82 388 13 50 96 71 135 263), lower := (rows 41 82 388 13 50 96 64 128 256), losses := [] }

theorem u25789 : Upper (D 6) (R 6) [40,80,384,5,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25790 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 82 388 14 21 33 98 226 354), lower := (rows 41 82 388 14 21 33 64 128 256), losses := [] }

theorem u25790 : Upper (D 6) (R 6) [40,80,384,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25791 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 41 82 388 14 21 34 97 225 353), lower := (rows 41 82 388 14 21 34 64 128 256), losses := [] }

theorem u25791 : Upper (D 6) (R 6) [40,80,384,6,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25792 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 97, targets := 4 },{ cop := 4, region := 98, targets := 4 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 41 82 388 14 21 96 99 163 291), lower := (rows 41 82 388 14 21 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 98 64 128 256), good := (rows 57 112 388 61 21 96 96 128 256) }] }

theorem u25792 : Upper (D 6) (R 6) [40,80,384,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25793 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 82 388 14 52 33 67 195 323), lower := (rows 41 82 388 14 52 33 64 128 256), losses := [] }

theorem u25793 : Upper (D 6) (R 6) [40,80,384,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25794 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 41 82 388 14 52 34 65 193 321), lower := (rows 41 82 388 14 52 34 64 128 256), losses := [] }

theorem u25794 : Upper (D 6) (R 6) [40,80,384,6,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25795 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(4,0)], upper := (rows 41 82 388 14 52 96 67 131 259), lower := (rows 41 82 388 14 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 98 64 128 256), good := (rows 56 114 388 62 52 96 96 128 256) },{ target := 1, region := (rows 9 0 4 8 24 98 64 128 256), good := (rows 57 112 388 61 52 96 96 128 256) }] }

theorem u25795 : Upper (D 6) (R 6) [40,80,384,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25796 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 82 388 73 52 33 70 134 262), lower := (rows 41 82 388 73 52 33 64 128 256), losses := [] }

theorem u25796 : Upper (D 6) (R 6) [40,80,384,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25797 : Route 9 := (fun mask => (mask,id))

def c25797 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25797 : Upper (D 6) (R 6) [40,80,384,65,36,2] 13 := by
  apply FastRouting.sound _ _ [40,80,384,65,36,2] 13 (by decide) (choices 1) [1,2,4] r25797 c25797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8016
  · exact u8017
  · exact u8018

def b25798 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 82 388 73 52 36 67 131 259), lower := (rows 41 82 388 73 52 36 64 128 256), losses := [] }

theorem u25798 : Upper (D 6) (R 6) [40,80,384,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25799 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 82 388 76 52 33 67 131 259), lower := (rows 41 82 388 76 52 33 64 128 256), losses := [] }

theorem u25799 : Upper (D 6) (R 6) [40,80,384,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25799
end Delivery.IrregularNine14.P06
