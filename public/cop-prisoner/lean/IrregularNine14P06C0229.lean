import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0048

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13740 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 265 82 33 100 228 356), lower := (rows 11 38 148 265 82 33 64 128 256), losses := [] }

theorem u13740 : Upper (D 6) (R 6) [10,36,144,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13741 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 265 82 36 97 225 353), lower := (rows 11 38 148 265 82 36 64 128 256), losses := [] }

theorem u13741 : Upper (D 6) (R 6) [10,36,144,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13742 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 265, targets := 64 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 38 148 265 82 96 101 165 293), lower := (rows 11 38 148 265 82 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 112 64 128 256), good := (rows 10 38 182 264 114 96 96 128 256) }] }

theorem u13742 : Upper (D 6) (R 6) [10,36,144,257,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13743 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 265 84 33 98 226 354), lower := (rows 11 38 148 265 84 33 64 128 256), losses := [] }

theorem u13743 : Upper (D 6) (R 6) [10,36,144,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13744 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 148 265 84 34 97 225 353), lower := (rows 11 38 148 265 84 34 64 128 256), losses := [] }

theorem u13744 : Upper (D 6) (R 6) [10,36,144,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13745 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 265, targets := 4 },{ cop := 1, region := 265, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 148 265 84 96 99 163 291), lower := (rows 11 38 148 265 84 96 64 128 256), losses := [] }

theorem u13745 : Upper (D 6) (R 6) [10,36,144,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13746 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 148 265 112 33 70 198 326), lower := (rows 11 38 148 265 112 33 64 128 256), losses := [] }

theorem u13746 : Upper (D 6) (R 6) [10,36,144,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13747 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 265 112 34 69 197 325), lower := (rows 11 38 148 265 112 34 64 128 256), losses := [] }

theorem u13747 : Upper (D 6) (R 6) [10,36,144,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13748 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 265 112 36 67 195 323), lower := (rows 11 38 148 265 112 36 64 128 256), losses := [] }

theorem u13748 : Upper (D 6) (R 6) [10,36,144,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13749 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 148 265 112 96 71 135 263), lower := (rows 11 38 148 265 112 96 64 128 256), losses := [] }

theorem u13749 : Upper (D 6) (R 6) [10,36,144,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13750 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 148 268 81 33 98 226 354), lower := (rows 11 38 148 268 81 33 64 128 256), losses := [] }

theorem u13750 : Upper (D 6) (R 6) [10,36,144,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13751 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 148 268 81 34 97 225 353), lower := (rows 11 38 148 268 81 34 64 128 256), losses := [] }

theorem u13751 : Upper (D 6) (R 6) [10,36,144,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13752 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 265, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 38 148 268 81 96 99 163 291), lower := (rows 11 38 148 268 81 96 64 128 256), losses := [] }

theorem u13752 : Upper (D 6) (R 6) [10,36,144,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13753 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 148 268 82 33 97 225 353), lower := (rows 11 38 148 268 82 33 64 128 256), losses := [] }

theorem u13753 : Upper (D 6) (R 6) [10,36,144,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13754 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 265, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 38 148 268 82 96 97 161 289), lower := (rows 11 38 148 268 82 96 64 128 256), losses := [] }

theorem u13754 : Upper (D 6) (R 6) [10,36,144,260,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13755 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 328, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 148 296 81 33 70 198 326), lower := (rows 11 38 148 296 81 33 64 128 256), losses := [] }

theorem u13755 : Upper (D 6) (R 6) [10,36,144,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13756 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 148 296 81 34 69 197 325), lower := (rows 11 38 148 296 81 34 64 128 256), losses := [] }

theorem u13756 : Upper (D 6) (R 6) [10,36,144,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13757 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 296 81 36 67 195 323), lower := (rows 11 38 148 296 81 36 64 128 256), losses := [] }

theorem u13757 : Upper (D 6) (R 6) [10,36,144,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13758 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 265, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 38 148 296 81 96 71 135 263), lower := (rows 11 38 148 296 81 96 64 128 256), losses := [] }

theorem u13758 : Upper (D 6) (R 6) [10,36,144,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13759 : Route 9 := (fun mask => (mask,id))

def c13759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13759 : Upper (D 6) (R 6) [10,36,144,288,66,1] 13 := by
  apply FastRouting.sound _ _ [10,36,144,288,66,1] 13 (by decide) (choices 1) [1,4] r13759 c13759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2915
  · exact u2916

def b13760 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 296 82 36 65 193 321), lower := (rows 11 38 148 296 82 36 64 128 256), losses := [] }

theorem u13760 : Upper (D 6) (R 6) [10,36,144,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13761 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 265, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 38 148 296 82 96 69 133 261), lower := (rows 11 38 148 296 82 96 64 128 256), losses := [] }

theorem u13761 : Upper (D 6) (R 6) [10,36,144,288,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13762 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 1, region := 328, targets := 1 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 11 38 148 328 21 33 98 226 354), lower := (rows 11 38 148 328 21 33 64 128 256), losses := [] }

theorem u13762 : Upper (D 6) (R 6) [10,36,144,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13763 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 148 328 21 34 97 225 353), lower := (rows 11 38 148 328 21 34 64 128 256), losses := [] }

theorem u13763 : Upper (D 6) (R 6) [10,36,144,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13764 : Route 9 := (fun mask => (mask,id))

def c13764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13764 : Upper (D 6) (R 6) [10,36,144,320,5,64] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,5,64] 13 (by decide) (choices 1) [1,2,32] r13764 c13764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2917
  · exact u2918
  · exact u2919

def b13765 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 148 328 49 33 70 198 326), lower := (rows 11 38 148 328 49 33 64 128 256), losses := [] }

theorem u13765 : Upper (D 6) (R 6) [10,36,144,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13766 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 148 328 49 34 69 197 325), lower := (rows 11 38 148 328 49 34 64 128 256), losses := [] }

theorem u13766 : Upper (D 6) (R 6) [10,36,144,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13767 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 328 49 36 67 195 323), lower := (rows 11 38 148 328 49 36 64 128 256), losses := [] }

theorem u13767 : Upper (D 6) (R 6) [10,36,144,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13768 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 4, region := 134, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 11 38 148 328 49 96 71 135 263), lower := (rows 11 38 148 328 49 96 64 128 256), losses := [] }

theorem u13768 : Upper (D 6) (R 6) [10,36,144,320,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13769 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 1, region := 328, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 11 38 148 328 81 33 102 166 294), lower := (rows 11 38 148 328 81 33 64 128 256), losses := [] }

theorem u13769 : Upper (D 6) (R 6) [10,36,144,320,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13770 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 11 38 148 328 81 34 101 165 293), lower := (rows 11 38 148 328 81 34 64 128 256), losses := [] }

theorem u13770 : Upper (D 6) (R 6) [10,36,144,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13771 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 328 81 36 99 163 291), lower := (rows 11 38 148 328 81 36 64 128 256), losses := [] }

theorem u13771 : Upper (D 6) (R 6) [10,36,144,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13772 : Route 9 := (fun mask => (mask,id))

def c13772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13772 : Upper (D 6) (R 6) [10,36,144,320,66,1] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,66,1] 13 (by decide) (choices 1) [1,4,32] r13772 c13772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2920
  · exact u2921
  · exact u2922

def b13773 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 328 82 36 97 161 289), lower := (rows 11 38 148 328 82 36 64 128 256), losses := [] }

theorem u13773 : Upper (D 6) (R 6) [10,36,144,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13774 : Route 9 := (fun mask => (mask,id))

def c13774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13774 : Upper (D 6) (R 6) [10,36,144,320,68,1] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,68,1] 13 (by decide) (choices 1) [1,2,32] r13774 c13774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2923
  · exact u2924
  · exact u2925

def b13775 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 148 328 84 34 97 161 289), lower := (rows 11 38 148 328 84 34 64 128 256), losses := [] }

theorem u13775 : Upper (D 6) (R 6) [10,36,144,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13776 : Route 9 := (fun mask => (mask,id))

def c13776 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13776 : Upper (D 6) (R 6) [10,36,144,320,96,1] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,96,1] 13 (by decide) (choices 1) [1,2,4] r13776 c13776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2926
  · exact u2927
  · exact u2928

def b13777 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 38 148 328 112 34 69 133 261), lower := (rows 11 38 148 328 112 34 64 128 256), losses := [] }

theorem u13777 : Upper (D 6) (R 6) [10,36,144,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13778 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 148 328 112 36 67 131 259), lower := (rows 11 38 148 328 112 36 64 128 256), losses := [] }

theorem u13778 : Upper (D 6) (R 6) [10,36,144,320,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13779 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 196 25 112 33 326 390 262), lower := (rows 11 38 196 25 112 33 64 128 256), losses := [] }

theorem u13779 : Upper (D 6) (R 6) [10,36,192,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13780 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 196 25 112 34 325 389 261), lower := (rows 11 38 196 25 112 34 64 128 256), losses := [] }

theorem u13780 : Upper (D 6) (R 6) [10,36,192,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13781 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 25 112 36 323 387 259), lower := (rows 11 38 196 25 112 36 64 128 256), losses := [] }

theorem u13781 : Upper (D 6) (R 6) [10,36,192,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13782 : Route 9 := (fun mask => (mask,id))

def c13782 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13782 : Upper (D 6) (R 6) [10,36,192,17,96,256] 13 := by
  apply FastRouting.sound _ _ [10,36,192,17,96,256] 13 (by decide) (choices 1) [1,2,4] r13782 c13782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2929
  · exact u2930
  · exact u2931

def b13783 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 196 25 276 33 98 226 354), lower := (rows 11 38 196 25 276 33 64 128 256), losses := [] }

theorem u13783 : Upper (D 6) (R 6) [10,36,192,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13784 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 196 25 276 34 97 225 353), lower := (rows 11 38 196 25 276 34 64 128 256), losses := [] }

theorem u13784 : Upper (D 6) (R 6) [10,36,192,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13785 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 25 276 96 99 163 291), lower := (rows 11 38 196 25 276 96 64 128 256), losses := [] }

theorem u13785 : Upper (D 6) (R 6) [10,36,192,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13786 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 196 25 304 33 70 198 326), lower := (rows 11 38 196 25 304 33 64 128 256), losses := [] }

theorem u13786 : Upper (D 6) (R 6) [10,36,192,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13787 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 196 25 304 34 69 197 325), lower := (rows 11 38 196 25 304 34 64 128 256), losses := [] }

theorem u13787 : Upper (D 6) (R 6) [10,36,192,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13788 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 25 304 36 67 195 323), lower := (rows 11 38 196 25 304 36 64 128 256), losses := [] }

theorem u13788 : Upper (D 6) (R 6) [10,36,192,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13789 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 25 304 96 71 135 263), lower := (rows 11 38 196 25 304 96 64 128 256), losses := [] }

theorem u13789 : Upper (D 6) (R 6) [10,36,192,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13790 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 196 25 336 33 102 166 294), lower := (rows 11 38 196 25 336 33 64 128 256), losses := [] }

theorem u13790 : Upper (D 6) (R 6) [10,36,192,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13791 : Route 9 := (fun mask => (mask,id))

def c13791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13791 : Upper (D 6) (R 6) [10,36,192,17,320,2] 13 := by
  apply FastRouting.sound _ _ [10,36,192,17,320,2] 13 (by decide) (choices 1) [1,4,32] r13791 c13791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2932
  · exact u2933
  · exact u2934

def b13792 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 25 336 36 99 163 291), lower := (rows 11 38 196 25 336 36 64 128 256), losses := [] }

theorem u13792 : Upper (D 6) (R 6) [10,36,192,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13793 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 5, region := 198, targets := 1 }], pairs := [(0,6),(1,0),(1,6)], upper := (rows 11 38 196 28 273 33 98 226 354), lower := (rows 11 38 196 28 273 33 64 128 256), losses := [] }

theorem u13793 : Upper (D 6) (R 6) [10,36,192,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13794 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 196 28 273 34 97 225 353), lower := (rows 11 38 196 28 273 34 64 128 256), losses := [] }

theorem u13794 : Upper (D 6) (R 6) [10,36,192,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13795 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 28 273 96 99 163 291), lower := (rows 11 38 196 28 273 96 64 128 256), losses := [] }

theorem u13795 : Upper (D 6) (R 6) [10,36,192,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13796 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 38 196 28 274 33 97 225 353), lower := (rows 11 38 196 28 274 33 64 128 256), losses := [] }

theorem u13796 : Upper (D 6) (R 6) [10,36,192,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13797 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 28 274 96 97 161 289), lower := (rows 11 38 196 28 274 96 64 128 256), losses := [] }

theorem u13797 : Upper (D 6) (R 6) [10,36,192,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13798 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 196 28 304 33 67 195 323), lower := (rows 11 38 196 28 304 33 64 128 256), losses := [] }

theorem u13798 : Upper (D 6) (R 6) [10,36,192,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13799 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 196 28 304 34 65 193 321), lower := (rows 11 38 196 28 304 34 64 128 256), losses := [] }

theorem u13799 : Upper (D 6) (R 6) [10,36,192,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13799
end Delivery.IrregularNine14.P06
