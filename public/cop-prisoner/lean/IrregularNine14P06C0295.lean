import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0082
import IrregularNine14P06C0083

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17700 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 100 328 22 36 81 145 273), lower := (rows 11 162 100 328 22 36 64 128 256), losses := [] }

theorem u17700 : Upper (D 6) (R 6) [10,160,96,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17701 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 100 328 22 48 69 133 261), lower := (rows 11 162 100 328 22 48 64 128 256), losses := [] }

theorem u17701 : Upper (D 6) (R 6) [10,160,96,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17701 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17702 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 25 84 34 100 228 356), lower := (rows 11 162 261 25 84 34 64 128 256), losses := [] }

theorem u17702 : Upper (D 6) (R 6) [10,160,257,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17703 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 5, region := 194, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 162 261 25 84 36 98 226 354), lower := (rows 11 162 261 25 84 36 64 128 256), losses := [] }

theorem u17703 : Upper (D 6) (R 6) [10,160,257,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17704 : Route 9 := (fun mask => (mask,id))

def c17704 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17704 : Upper (D 6) (R 6) [10,160,257,17,68,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,17,68,64] 13 (by decide) (choices 1) [2,4,32] r17704 c17704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4949
  · exact u4950
  · exact u4951

def b17705 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 28 81 34 100 228 356), lower := (rows 11 162 261 28 81 34 64 128 256), losses := [] }

theorem u17705 : Upper (D 6) (R 6) [10,160,257,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17706 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 194, targets := 5 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 11 162 261 28 81 36 98 226 354), lower := (rows 11 162 261 28 81 36 64 128 256), losses := [{ target := 2, region := (rows 1 34 0 8 17 32 98 162 290), good := (rows 475 482 273 24 81 482 64 128 256) }] }

theorem u17706 : Upper (D 6) (R 6) [10,160,257,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17707 : Route 9 := (fun mask => (mask,id))

def c17707 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17707 : Upper (D 6) (R 6) [10,160,257,20,65,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20,65,64] 13 (by decide) (choices 1) [2,4,32] r17707 c17707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4952
  · exact u4953
  · exact u4954

def r17708 : Route 9 := (fun mask => (mask,id))

def c17708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17708 : Upper (D 6) (R 6) [10,160,257,20,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20,66,1] 13 (by decide) (choices 1) [4,32] r17708 c17708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4955
  · exact u4956

def r17709 : Route 9 := (fun mask => (mask,id))

def c17709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17709 : Upper (D 6) (R 6) [10,160,257,20,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20,66,4] 13 (by decide) (choices 1) [1,32] r17709 c17709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4957
  · exact u4958

def r17710 : Route 9 := (fun mask => (mask,id))

def c17710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17710 : Upper (D 6) (R 6) [10,160,257,20,66,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20,66,64] 13 (by decide) (choices 1) [1,4,32] r17710 c17710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4959
  · exact u4960
  · exact u4961

def r17711 : Route 9 := (fun mask => (mask,id))

def c17711 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17711 : Upper (D 6) (R 6) [10,160,257,20,96,1] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20,96,1] 13 (by decide) (choices 1) [2,4] r17711 c17711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4962
  · exact u4963

def b17712 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 28 112 34 69 197 325), lower := (rows 11 162 261 28 112 34 64 128 256), losses := [] }

theorem u17712 : Upper (D 6) (R 6) [10,160,257,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17713 : Route 9 := (fun mask => (mask,id))

def c17713 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17713 : Upper (D 6) (R 6) [10,160,257,20,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20,96,4] 13 (by decide) (choices 1) [1,2] r17713 c17713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4964
  · exact u4965

def b17714 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 261 28 112 96 71 135 263), lower := (rows 11 162 261 28 112 96 64 128 256), losses := [] }

theorem u17714 : Upper (D 6) (R 6) [10,160,257,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17715 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 261 44 22 33 80 208 336), lower := (rows 11 162 261 44 22 33 64 128 256), losses := [] }

theorem u17715 : Upper (D 6) (R 6) [10,160,257,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17716 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 261 44 22 48 65 193 321), lower := (rows 11 162 261 44 22 48 64 128 256), losses := [] }

theorem u17716 : Upper (D 6) (R 6) [10,160,257,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17716 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17717 : Route 9 := (fun mask => (mask,id))

def c17717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17717 : Upper (D 6) (R 6) [10,160,257,36,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,36,6,64] 13 (by decide) (choices 1) [1,16] r17717 c17717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4966
  · exact u4967

def b17718 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 261 44 81 34 84 212 340), lower := (rows 11 162 261 44 81 34 64 128 256), losses := [] }

theorem u17718 : Upper (D 6) (R 6) [10,160,257,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17719 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 261 44 81 36 82 210 338), lower := (rows 11 162 261 44 81 36 64 128 256), losses := [] }

theorem u17719 : Upper (D 6) (R 6) [10,160,257,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17720 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 261 44 81 48 70 198 326), lower := (rows 11 162 261 44 81 48 64 128 256), losses := [] }

theorem u17720 : Upper (D 6) (R 6) [10,160,257,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17720 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17721 : Route 9 := (fun mask => (mask,id))

def c17721 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17721 : Upper (D 6) (R 6) [10,160,257,36,65,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,36,65,64] 13 (by decide) (choices 1) [2,4,16] r17721 c17721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4968
  · exact u4969
  · exact u4970

def b17722 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 261 44 82 33 84 212 340), lower := (rows 11 162 261 44 82 33 64 128 256), losses := [] }

theorem u17722 : Upper (D 6) (R 6) [10,160,257,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17723 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 261 44 82 36 81 209 337), lower := (rows 11 162 261 44 82 36 64 128 256), losses := [] }

theorem u17723 : Upper (D 6) (R 6) [10,160,257,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17724 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 261 44 82 48 69 197 325), lower := (rows 11 162 261 44 82 48 64 128 256), losses := [] }

theorem u17724 : Upper (D 6) (R 6) [10,160,257,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17724 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17725 : Route 9 := (fun mask => (mask,id))

def c17725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17725 : Upper (D 6) (R 6) [10,160,257,36,66,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,36,66,64] 13 (by decide) (choices 1) [1,4,16] r17725 c17725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4971
  · exact u4972
  · exact u4973

def b17726 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 261 44 84 33 82 210 338), lower := (rows 11 162 261 44 84 33 64 128 256), losses := [] }

theorem u17726 : Upper (D 6) (R 6) [10,160,257,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17727 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 261 44 84 34 81 209 337), lower := (rows 11 162 261 44 84 34 64 128 256), losses := [] }

theorem u17727 : Upper (D 6) (R 6) [10,160,257,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17728 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 261 44 84 48 67 195 323), lower := (rows 11 162 261 44 84 48 64 128 256), losses := [] }

theorem u17728 : Upper (D 6) (R 6) [10,160,257,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17728 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17729 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 261 44 84 96 83 147 275), lower := (rows 11 162 261 44 84 96 64 128 256), losses := [] }

theorem u17729 : Upper (D 6) (R 6) [10,160,257,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17730 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 261 56 84 33 70 198 326), lower := (rows 11 162 261 56 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 64 128 256), good := (rows 41 160 293 56 124 33 64 128 256) }] }

theorem u17730 : Upper (D 6) (R 6) [10,160,257,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17731 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 261 56 84 34 69 197 325), lower := (rows 11 162 261 56 84 34 64 128 256), losses := [] }

theorem u17731 : Upper (D 6) (R 6) [10,160,257,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17732 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 261 56 84 36 67 195 323), lower := (rows 11 162 261 56 84 36 64 128 256), losses := [] }

theorem u17732 : Upper (D 6) (R 6) [10,160,257,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17733 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 261 56 84 96 71 135 263), lower := (rows 11 162 261 56 84 96 64 128 256), losses := [] }

theorem u17733 : Upper (D 6) (R 6) [10,160,257,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17734 : Route 9 := (fun mask => (mask,id))

def c17734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17734 : Upper (D 6) (R 6) [10,160,257,65,6,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,65,6,4] 13 (by decide) (choices 1) [16,32] r17734 c17734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4974
  · exact u4975

def b17735 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 162 261 73 22 48 100 228 356), lower := (rows 11 162 261 73 22 48 64 128 256), losses := [] }

theorem u17735 : Upper (D 6) (R 6) [10,160,257,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17735 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17736 : Route 9 := (fun mask => (mask,id))

def c17736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17736 : Upper (D 6) (R 6) [10,160,257,65,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,65,6,64] 13 (by decide) (choices 1) [4,16,32] r17736 c17736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4976
  · exact u4977
  · exact u4978

def b17737 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 73 52 34 84 212 340), lower := (rows 11 162 261 73 52 34 64 128 256), losses := [] }

theorem u17737 : Upper (D 6) (R 6) [10,160,257,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17738 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 261 73 52 36 82 210 338), lower := (rows 11 162 261 73 52 36 64 128 256), losses := [] }

theorem u17738 : Upper (D 6) (R 6) [10,160,257,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17739 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 261 73 52 48 70 198 326), lower := (rows 11 162 261 73 52 48 64 128 256), losses := [] }

theorem u17739 : Upper (D 6) (R 6) [10,160,257,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17739 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17740 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 4, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 162 261 73 52 96 86 150 278), lower := (rows 11 162 261 73 52 96 64 128 256), losses := [] }

theorem u17740 : Upper (D 6) (R 6) [10,160,257,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17741 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 73 112 34 84 148 276), lower := (rows 11 162 261 73 112 34 64 128 256), losses := [] }

theorem u17741 : Upper (D 6) (R 6) [10,160,257,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17742 : Route 9 := (fun mask => (mask,id))

def c17742 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17742 : Upper (D 6) (R 6) [10,160,257,65,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,65,96,4] 13 (by decide) (choices 1) [2,4,16] r17742 c17742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4979
  · exact u4980
  · exact u4981

def b17743 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 261 73 112 48 70 134 262), lower := (rows 11 162 261 73 112 48 64 128 256), losses := [] }

theorem u17743 : Upper (D 6) (R 6) [10,160,257,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17743 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17744 : Route 9 := (fun mask => (mask,id))

def c17744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17744 : Upper (D 6) (R 6) [10,160,257,68,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,6,1] 13 (by decide) (choices 1) [16,32] r17744 c17744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4982
  · exact u4983

def r17745 : Route 9 := (fun mask => (mask,id))

def c17745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17745 : Upper (D 6) (R 6) [10,160,257,68,6,16] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,6,16] 13 (by decide) (choices 1) [1,32] r17745 c17745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4984
  · exact u4985

def r17746 : Route 9 := (fun mask => (mask,id))

def c17746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17746 : Upper (D 6) (R 6) [10,160,257,68,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,6,64] 13 (by decide) (choices 1) [1,16,32] r17746 c17746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4986
  · exact u4987
  · exact u4988

def b17747 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 261 76 49 34 84 212 340), lower := (rows 11 162 261 76 49 34 64 128 256), losses := [] }

theorem u17747 : Upper (D 6) (R 6) [10,160,257,68,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17748 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 162 261 76 49 36 82 210 338), lower := (rows 11 162 261 76 49 36 64 128 256), losses := [] }

theorem u17748 : Upper (D 6) (R 6) [10,160,257,68,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17749 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 261 76 49 48 70 198 326), lower := (rows 11 162 261 76 49 48 64 128 256), losses := [] }

theorem u17749 : Upper (D 6) (R 6) [10,160,257,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17749 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17750 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 162 261 76 49 96 86 150 278), lower := (rows 11 162 261 76 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 104 64 128 256), good := (rows 57 160 277 108 49 96 96 128 256) }] }

theorem u17750 : Upper (D 6) (R 6) [10,160,257,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17751 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 162 261 76 52 33 82 210 338), lower := (rows 11 162 261 76 52 33 64 128 256), losses := [] }

theorem u17751 : Upper (D 6) (R 6) [10,160,257,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17752 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 76 52 34 81 209 337), lower := (rows 11 162 261 76 52 34 64 128 256), losses := [] }

theorem u17752 : Upper (D 6) (R 6) [10,160,257,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17753 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 261 76 52 48 67 195 323), lower := (rows 11 162 261 76 52 48 64 128 256), losses := [] }

theorem u17753 : Upper (D 6) (R 6) [10,160,257,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17753 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17754 : Route 9 := (fun mask => (mask,id))

def c17754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17754 : Upper (D 6) (R 6) [10,160,257,68,36,64] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,36,64] 13 (by decide) (choices 1) [1,2,16] r17754 c17754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4989
  · exact u4990
  · exact u4991

def b17755 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 261 76 81 34 116 180 308), lower := (rows 11 162 261 76 81 34 64 128 256), losses := [] }

theorem u17755 : Upper (D 6) (R 6) [10,160,257,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17756 : Route 9 := (fun mask => (mask,id))

def c17756 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17756 : Upper (D 6) (R 6) [10,160,257,68,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,65,4] 13 (by decide) (choices 1) [2,16,32] r17756 c17756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4992
  · exact u4993
  · exact u4994

def b17757 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 162 261 76 81 48 102 166 294), lower := (rows 11 162 261 76 81 48 64 128 256), losses := [] }

theorem u17757 : Upper (D 6) (R 6) [10,160,257,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17757 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17758 : Route 9 := (fun mask => (mask,id))

def c17758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17758 : Upper (D 6) (R 6) [10,160,257,68,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,66,1] 13 (by decide) (choices 1) [4,16,32] r17758 c17758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4995
  · exact u4996
  · exact u4997

def r17759 : Route 9 := (fun mask => (mask,id))

def c17759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17759 : Upper (D 6) (R 6) [10,160,257,68,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68,66,4] 13 (by decide) (choices 1) [1,16,32] r17759 c17759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4998
  · exact u4999
  · exact u5000

#print axioms u17759
end Delivery.IrregularNine14.P06
