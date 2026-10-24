import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0150
import IrregularNine14P07C0151

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25740 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 28 74 176 33 194 194 450), lower := (rows 37 259 28 74 176 33 64 128 256), losses := [] }

theorem u25740 : Upper (D 7) (R 7) [36,257,24,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25741 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 259 28 74 176 34 193 193 449), lower := (rows 37 259 28 74 176 34 64 128 256), losses := [{ target := 5, region := (rows 1 3 20 43 16 0 67 131 259), good := (rows 463 459 28 458 156 458 64 128 256) }] }

theorem u25741 : Upper (D 7) (R 7) [36,257,24,66,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25742 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,5),(1,6),(3,5),(4,6)], upper := (rows 37 259 28 74 176 96 195 131 387), lower := (rows 37 259 28 74 176 96 64 128 256), losses := [] }

theorem u25742 : Upper (D 7) (R 7) [36,257,24,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25743 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 28 74 176 160 67 195 323), lower := (rows 37 259 28 74 176 160 64 128 256), losses := [] }

theorem u25743 : Upper (D 7) (R 7) [36,257,24,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25744 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 259 28 74 208 33 226 162 418), lower := (rows 37 259 28 74 208 33 64 128 256), losses := [] }

theorem u25744 : Upper (D 7) (R 7) [36,257,24,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25745 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 37 259 28 74 208 34 225 161 417), lower := (rows 37 259 28 74 208 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 32 65 129 257), good := (rows 501 465 28 92 208 48 64 128 256) }] }

theorem u25745 : Upper (D 7) (R 7) [36,257,24,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25746 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(3,7)], upper := (rows 37 259 28 74 208 160 99 163 291), lower := (rows 37 259 28 74 208 160 64 128 256), losses := [] }

theorem u25746 : Upper (D 7) (R 7) [36,257,24,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25747 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 26 152 34 224 224 480), lower := (rows 37 259 69 26 152 34 64 128 256), losses := [] }

theorem u25747 : Upper (D 7) (R 7) [36,257,65,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25748 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 26 152 96 226 162 418), lower := (rows 37 259 69 26 152 96 64 128 256), losses := [] }

theorem u25748 : Upper (D 7) (R 7) [36,257,65,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25749 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 69 26 152 160 98 226 354), lower := (rows 37 259 69 26 152 160 64 128 256), losses := [] }

theorem u25749 : Upper (D 7) (R 7) [36,257,65,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25750 : Route 9 := (fun mask => (mask,id))

def c25750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25750 : Upper (D 7) (R 7) [36,257,65,18,160,2] 13 := by
  apply FastRouting.sound _ _ [36,257,65,18,160,2] 13 (by decide) (choices 1) [8,128] r25750 c25750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9046
  · exact u9047

def b25751 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 248, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 37 259 69 26 176 40 194 194 450), lower := (rows 37 259 69 26 176 40 64 128 256), losses := [] }

theorem u25751 : Upper (D 7) (R 7) [36,257,65,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25751 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25752 : PairBound 9 := { available := 138, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 26 176 96 202 138 394), lower := (rows 37 259 69 26 176 96 64 128 256), losses := [] }

theorem u25752 : Upper (D 7) (R 7) [36,257,65,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25753 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 69 26 176 160 74 202 330), lower := (rows 37 259 69 26 176 160 64 128 256), losses := [] }

theorem u25753 : Upper (D 7) (R 7) [36,257,65,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25754 : Route 9 := (fun mask => (mask,id))

def c25754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25754 : Upper (D 7) (R 7) [36,257,65,18,192,2] 13 := by
  apply FastRouting.sound _ _ [36,257,65,18,192,2] 13 (by decide) (choices 1) [8,32,128] r25754 c25754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9048
  · exact u9049
  · exact u9050

def b25755 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 37 259 69 26 208 40 226 162 418), lower := (rows 37 259 69 26 208 40 64 128 256), losses := [] }

theorem u25755 : Upper (D 7) (R 7) [36,257,65,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25755 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25756 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 26 208 160 106 170 298), lower := (rows 37 259 69 26 208 160 64 128 256), losses := [] }

theorem u25756 : Upper (D 7) (R 7) [36,257,65,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25757 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 213, targets := 2 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 37 259 69 42 88 34 208 144 400), lower := (rows 37 259 69 42 88 34 64 128 256), losses := [] }

theorem u25757 : Upper (D 7) (R 7) [36,257,65,34,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25758 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 42 88 48 194 130 386), lower := (rows 37 259 69 42 88 48 64 128 256), losses := [] }

theorem u25758 : Upper (D 7) (R 7) [36,257,65,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25758 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25759 : Route 9 := (fun mask => (mask,id))

def c25759 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25759 : Upper (D 7) (R 7) [36,257,65,34,72,128] 13 := by
  apply FastRouting.sound _ _ [36,257,65,34,72,128] 13 (by decide) (choices 1) [2,16,128] r25759 c25759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9051
  · exact u9052
  · exact u9053

def b25760 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 69 42 146 40 208 208 464), lower := (rows 37 259 69 42 146 40 64 128 256), losses := [] }

theorem u25760 : Upper (D 7) (R 7) [36,257,65,34,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25760 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25761 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 197, targets := 2 }], pairs := [(0,1),(3,0),(4,0)], upper := (rows 37 259 69 42 146 48 200 200 456), lower := (rows 37 259 69 42 146 48 64 128 256), losses := [] }

theorem u25761 : Upper (D 7) (R 7) [36,257,65,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25761 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25762 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 42 146 96 216 152 408), lower := (rows 37 259 69 42 146 96 64 128 256), losses := [] }

theorem u25762 : Upper (D 7) (R 7) [36,257,65,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25763 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 208, targets := 32 },{ cop := 4, region := 40, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,5)], upper := (rows 37 259 69 42 146 160 88 216 344), lower := (rows 37 259 69 42 146 160 64 128 256), losses := [] }

theorem u25763 : Upper (D 7) (R 7) [36,257,65,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25764 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 213, targets := 2 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 37 259 69 42 152 34 208 208 464), lower := (rows 37 259 69 42 152 34 64 128 256), losses := [] }

theorem u25764 : Upper (D 7) (R 7) [36,257,65,34,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25765 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 248, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 37 259 69 42 152 48 194 194 450), lower := (rows 37 259 69 42 152 48 64 128 256), losses := [] }

theorem u25765 : Upper (D 7) (R 7) [36,257,65,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25765 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25766 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 42 152 96 210 146 402), lower := (rows 37 259 69 42 152 96 64 128 256), losses := [] }

theorem u25766 : Upper (D 7) (R 7) [36,257,65,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25767 : Route 9 := (fun mask => (mask,id))

def c25767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25767 : Upper (D 7) (R 7) [36,257,65,34,136,128] 13 := by
  apply FastRouting.sound _ _ [36,257,65,34,136,128] 13 (by decide) (choices 1) [2,16] r25767 c25767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9054
  · exact u9055

def b25768 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 213, targets := 2 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 37 259 69 42 208 34 216 152 408), lower := (rows 37 259 69 42 208 34 64 128 256), losses := [] }

theorem u25768 : Upper (D 7) (R 7) [36,257,65,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25769 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 69 42 208 40 210 146 402), lower := (rows 37 259 69 42 208 40 64 128 256), losses := [] }

theorem u25769 : Upper (D 7) (R 7) [36,257,65,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25769 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25770 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 42 208 48 202 138 394), lower := (rows 37 259 69 42 208 48 64 128 256), losses := [] }

theorem u25770 : Upper (D 7) (R 7) [36,257,65,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25770 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25771 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 42 208 160 90 154 282), lower := (rows 37 259 69 42 208 160 64 128 256), losses := [] }

theorem u25771 : Upper (D 7) (R 7) [36,257,65,34,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25772 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 37 259 69 56 82 34 200 136 392), lower := (rows 37 259 69 56 82 34 64 128 256), losses := [] }

theorem u25772 : Upper (D 7) (R 7) [36,257,65,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25773 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 56 82 40 194 130 386), lower := (rows 37 259 69 56 82 40 64 128 256), losses := [] }

theorem u25773 : Upper (D 7) (R 7) [36,257,65,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25773 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25774 : Route 9 := (fun mask => (mask,id))

def c25774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25774 : Upper (D 7) (R 7) [36,257,65,48,66,128] 13 := by
  apply FastRouting.sound _ _ [36,257,65,48,66,128] 13 (by decide) (choices 1) [2,8,128] r25774 c25774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9056
  · exact u9057
  · exact u9058

def b25775 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 56 146 34 200 200 456), lower := (rows 37 259 69 56 146 34 64 128 256), losses := [] }

theorem u25775 : Upper (D 7) (R 7) [36,257,65,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25776 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 69 56 146 40 194 194 450), lower := (rows 37 259 69 56 146 40 64 128 256), losses := [] }

theorem u25776 : Upper (D 7) (R 7) [36,257,65,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25776 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25777 : PairBound 9 := { available := 138, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 56 146 96 202 138 394), lower := (rows 37 259 69 56 146 96 64 128 256), losses := [] }

theorem u25777 : Upper (D 7) (R 7) [36,257,65,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25778 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 69 56 146 160 74 202 330), lower := (rows 37 259 69 56 146 160 64 128 256), losses := [] }

theorem u25778 : Upper (D 7) (R 7) [36,257,65,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25779 : Route 9 := (fun mask => (mask,id))

def c25779 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25779 : Upper (D 7) (R 7) [36,257,65,48,192,2] 13 := by
  apply FastRouting.sound _ _ [36,257,65,48,192,2] 13 (by decide) (choices 1) [2,8,128] r25779 c25779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9059
  · exact u9060
  · exact u9061

def b25780 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 56 208 40 194 130 386), lower := (rows 37 259 69 56 208 40 64 128 256), losses := [] }

theorem u25780 : Upper (D 7) (R 7) [36,257,65,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25780 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25781 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 259 69 56 208 160 74 138 266), lower := (rows 37 259 69 56 208 160 64 128 256), losses := [] }

theorem u25781 : Upper (D 7) (R 7) [36,257,65,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25782 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 74 146 40 240 176 432), lower := (rows 37 259 69 74 146 40 64 128 256), losses := [] }

theorem u25782 : Upper (D 7) (R 7) [36,257,65,66,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25782 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25783 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 176, targets := 64 }], pairs := [(3,0),(4,0),(4,6)], upper := (rows 37 259 69 74 146 48 232 168 424), lower := (rows 37 259 69 74 146 48 64 128 256), losses := [] }

theorem u25783 : Upper (D 7) (R 7) [36,257,65,66,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25783 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25784 : Route 9 := (fun mask => (mask,id))

def c25784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25784 : Upper (D 7) (R 7) [36,257,65,66,130,128] 13 := by
  apply FastRouting.sound _ _ [36,257,65,66,130,128] 13 (by decide) (choices 1) [8,16,32] r25784 c25784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9062
  · exact u9063
  · exact u9064

def b25785 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(4,0)], upper := (rows 37 259 69 74 152 34 240 176 432), lower := (rows 37 259 69 74 152 34 64 128 256), losses := [] }

theorem u25785 : Upper (D 7) (R 7) [36,257,65,66,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25786 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 37 259 69 74 152 48 226 162 418), lower := (rows 37 259 69 74 152 48 64 128 256), losses := [] }

theorem u25786 : Upper (D 7) (R 7) [36,257,65,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25786 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25787 : Route 9 := (fun mask => (mask,id))

def c25787 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25787 : Upper (D 7) (R 7) [36,257,65,66,136,128] 13 := by
  apply FastRouting.sound _ _ [36,257,65,66,136,128] 13 (by decide) (choices 1) [2,16,32] r25787 c25787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9065
  · exact u9066
  · exact u9067

def b25788 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(4,0)], upper := (rows 37 259 69 74 176 34 216 152 408), lower := (rows 37 259 69 74 176 34 64 128 256), losses := [] }

theorem u25788 : Upper (D 7) (R 7) [36,257,65,66,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25789 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 74 176 40 210 146 402), lower := (rows 37 259 69 74 176 40 64 128 256), losses := [] }

theorem u25789 : Upper (D 7) (R 7) [36,257,65,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25789 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25790 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 69 74 176 48 202 138 394), lower := (rows 37 259 69 74 176 48 64 128 256), losses := [] }

theorem u25790 : Upper (D 7) (R 7) [36,257,65,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25790 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25791 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 69 74 176 160 90 154 282), lower := (rows 37 259 69 74 176 160 64 128 256), losses := [] }

theorem u25791 : Upper (D 7) (R 7) [36,257,65,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25792 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,0)], upper := (rows 37 259 69 88 146 34 232 168 424), lower := (rows 37 259 69 88 146 34 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 16 50 64 0 256), good := (rows 37 291 69 125 50 34 64 0 256) }] }

theorem u25792 : Upper (D 7) (R 7) [36,257,65,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25793 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 88 146 40 226 162 418), lower := (rows 37 259 69 88 146 40 64 128 256), losses := [] }

theorem u25793 : Upper (D 7) (R 7) [36,257,65,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25793 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25794 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 88 146 160 106 170 298), lower := (rows 37 259 69 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 257 69 125 176 160 64 160 256) }] }

theorem u25794 : Upper (D 7) (R 7) [36,257,65,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25795 : Route 9 := (fun mask => (mask,id))

def c25795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25795 : Upper (D 7) (R 7) [36,257,65,80,160,2] 13 := by
  apply FastRouting.sound _ _ [36,257,65,80,160,2] 13 (by decide) (choices 1) [2,8,128] r25795 c25795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9068
  · exact u9069
  · exact u9070

def b25796 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 88 176 40 194 130 386), lower := (rows 37 259 69 88 176 40 64 128 256), losses := [] }

theorem u25796 : Upper (D 7) (R 7) [36,257,65,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25796 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25797 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 69 88 176 160 74 138 266), lower := (rows 37 259 69 88 176 160 64 128 256), losses := [] }

theorem u25797 : Upper (D 7) (R 7) [36,257,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25798 : Route 9 := (fun mask => (mask,id))

def c25798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25798 : Upper (D 7) (R 7) [36,257,65,130,160,2] 13 := by
  apply FastRouting.sound _ _ [36,257,65,130,160,2] 13 (by decide) (choices 1) [8,16] r25798 c25798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9071
  · exact u9072

def b25799 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 69 138 176 40 82 210 338), lower := (rows 37 259 69 138 176 40 64 128 256), losses := [] }

theorem u25799 : Upper (D 7) (R 7) [36,257,65,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25799 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25799
end Delivery.IrregularNine14.P07
