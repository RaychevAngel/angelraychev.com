import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0116

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22800 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 26 28 33 100 228 356), lower := (rows 35 131 324 26 28 33 64 128 256), losses := [] }

theorem u22800 : Upper (D 6) (R 6) [34,129,320,18,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22801 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 131 324 26 28 36 97 225 353), lower := (rows 35 131 324 26 28 36 64 128 256), losses := [] }

theorem u22801 : Upper (D 6) (R 6) [34,129,320,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22802 : Route 9 := (fun mask => (mask,id))

def c22802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22802 : Upper (D 6) (R 6) [34,129,320,18,12,64] 13 := by
  apply FastRouting.sound _ _ [34,129,320,18,12,64] 13 (by decide) (choices 1) [1,4,32] r22802 c22802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6975
  · exact u6976
  · exact u6977

def b22803 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 26 52 33 76 204 332), lower := (rows 35 131 324 26 52 33 64 128 256), losses := [] }

theorem u22803 : Upper (D 6) (R 6) [34,129,320,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22804 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 324 26 52 36 73 201 329), lower := (rows 35 131 324 26 52 36 64 128 256), losses := [] }

theorem u22804 : Upper (D 6) (R 6) [34,129,320,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22805 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 324 26 52 40 69 197 325), lower := (rows 35 131 324 26 52 40 64 128 256), losses := [] }

theorem u22805 : Upper (D 6) (R 6) [34,129,320,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22805 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22806 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 324 26 52 96 77 141 269), lower := (rows 35 131 324 26 52 96 64 128 256), losses := [] }

theorem u22806 : Upper (D 6) (R 6) [34,129,320,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22807 : Route 9 := (fun mask => (mask,id))

def c22807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22807 : Upper (D 6) (R 6) [34,129,320,18,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,18,65,4] 13 (by decide) (choices 1) [4,8,32] r22807 c22807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6978
  · exact u6979
  · exact u6980

def b22808 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 324 26 81 40 100 164 292), lower := (rows 35 131 324 26 81 40 64 128 256), losses := [] }

theorem u22808 : Upper (D 6) (R 6) [34,129,320,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22808 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22809 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 26 112 33 76 140 268), lower := (rows 35 131 324 26 112 33 64 128 256), losses := [] }

theorem u22809 : Upper (D 6) (R 6) [34,129,320,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22810 : Route 9 := (fun mask => (mask,id))

def c22810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22810 : Upper (D 6) (R 6) [34,129,320,18,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,18,96,4] 13 (by decide) (choices 1) [1,4,8] r22810 c22810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6981
  · exact u6982
  · exact u6983

def b22811 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 324 26 112 40 69 133 261), lower := (rows 35 131 324 26 112 40 64 128 256), losses := [] }

theorem u22811 : Upper (D 6) (R 6) [34,129,320,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22811 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22812 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 28 56 33 70 198 326), lower := (rows 35 131 324 28 56 33 64 128 256), losses := [] }

theorem u22812 : Upper (D 6) (R 6) [34,129,320,20,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22813 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 28 56 34 69 197 325), lower := (rows 35 131 324 28 56 34 64 128 256), losses := [] }

theorem u22813 : Upper (D 6) (R 6) [34,129,320,20,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22814 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 56, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 324 28 56 36 67 195 323), lower := (rows 35 131 324 28 56 36 64 128 256), losses := [] }

theorem u22814 : Upper (D 6) (R 6) [34,129,320,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22815 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 324 28 56 96 71 135 263), lower := (rows 35 131 324 28 56 96 64 128 256), losses := [] }

theorem u22815 : Upper (D 6) (R 6) [34,129,320,20,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22816 : PairBound 9 := { available := 44, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 28 81 34 108 172 300), lower := (rows 35 131 324 28 81 34 64 128 256), losses := [] }

theorem u22816 : Upper (D 6) (R 6) [34,129,320,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22817 : Route 9 := (fun mask => (mask,id))

def c22817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22817 : Upper (D 6) (R 6) [34,129,320,20,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,20,65,4] 13 (by decide) (choices 1) [2,8,32] r22817 c22817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6984
  · exact u6985
  · exact u6986

def b22818 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 324 28 81 40 102 166 294), lower := (rows 35 131 324 28 81 40 64 128 256), losses := [] }

theorem u22818 : Upper (D 6) (R 6) [34,129,320,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22818 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22819 : PairBound 9 := { available := 44, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 28 82 33 108 172 300), lower := (rows 35 131 324 28 82 33 64 128 256), losses := [] }

theorem u22819 : Upper (D 6) (R 6) [34,129,320,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22820 : Route 9 := (fun mask => (mask,id))

def c22820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22820 : Upper (D 6) (R 6) [34,129,320,20,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,20,66,4] 13 (by decide) (choices 1) [1,8,32] r22820 c22820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6987
  · exact u6988
  · exact u6989

def b22821 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 324 28 82 40 101 165 293), lower := (rows 35 131 324 28 82 40 64 128 256), losses := [] }

theorem u22821 : Upper (D 6) (R 6) [34,129,320,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22821 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22822 : PairBound 9 := { available := 14, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 28 112 33 78 142 270), lower := (rows 35 131 324 28 112 33 64 128 256), losses := [] }

theorem u22822 : Upper (D 6) (R 6) [34,129,320,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22823 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 28 112 34 77 141 269), lower := (rows 35 131 324 28 112 34 64 128 256), losses := [] }

theorem u22823 : Upper (D 6) (R 6) [34,129,320,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22824 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 324 28 112 36 75 139 267), lower := (rows 35 131 324 28 112 36 64 128 256), losses := [] }

theorem u22824 : Upper (D 6) (R 6) [34,129,320,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22825 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 324 28 112 40 71 135 263), lower := (rows 35 131 324 28 112 40 64 128 256), losses := [] }

theorem u22825 : Upper (D 6) (R 6) [34,129,320,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22825 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22826 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 44 81 34 92 156 284), lower := (rows 35 131 324 44 81 34 64 128 256), losses := [] }

theorem u22826 : Upper (D 6) (R 6) [34,129,320,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22827 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 324 44 81 36 90 154 282), lower := (rows 35 131 324 44 81 36 64 128 256), losses := [] }

theorem u22827 : Upper (D 6) (R 6) [34,129,320,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22828 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 324 44 81 40 86 150 278), lower := (rows 35 131 324 44 81 40 64 128 256), losses := [] }

theorem u22828 : Upper (D 6) (R 6) [34,129,320,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22828 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22829 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 324 44 81 48 78 142 270), lower := (rows 35 131 324 44 81 48 64 128 256), losses := [] }

theorem u22829 : Upper (D 6) (R 6) [34,129,320,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22829 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22830 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 44 82 33 92 156 284), lower := (rows 35 131 324 44 82 33 64 128 256), losses := [] }

theorem u22830 : Upper (D 6) (R 6) [34,129,320,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22831 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 131 324 44 82 36 89 153 281), lower := (rows 35 131 324 44 82 36 64 128 256), losses := [] }

theorem u22831 : Upper (D 6) (R 6) [34,129,320,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22832 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 324 44 82 40 85 149 277), lower := (rows 35 131 324 44 82 40 64 128 256), losses := [] }

theorem u22832 : Upper (D 6) (R 6) [34,129,320,36,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22832 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22833 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 324 44 82 48 77 141 269), lower := (rows 35 131 324 44 82 48 64 128 256), losses := [] }

theorem u22833 : Upper (D 6) (R 6) [34,129,320,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22833 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22834 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 44 88 33 86 150 278), lower := (rows 35 131 324 44 88 33 64 128 256), losses := [] }

theorem u22834 : Upper (D 6) (R 6) [34,129,320,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22835 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 44 88 34 85 149 277), lower := (rows 35 131 324 44 88 34 64 128 256), losses := [] }

theorem u22835 : Upper (D 6) (R 6) [34,129,320,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22836 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 324 44 88 36 83 147 275), lower := (rows 35 131 324 44 88 36 64 128 256), losses := [] }

theorem u22836 : Upper (D 6) (R 6) [34,129,320,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22837 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 324 44 88 48 71 135 263), lower := (rows 35 131 324 44 88 48 64 128 256), losses := [] }

theorem u22837 : Upper (D 6) (R 6) [34,129,320,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22837 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22838 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 56 81 34 76 140 268), lower := (rows 35 131 324 56 81 34 64 128 256), losses := [] }

theorem u22838 : Upper (D 6) (R 6) [34,129,320,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22839 : Route 9 := (fun mask => (mask,id))

def c22839 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22839 : Upper (D 6) (R 6) [34,129,320,48,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,48,65,4] 13 (by decide) (choices 1) [2,4,8] r22839 c22839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6990
  · exact u6991
  · exact u6992

def b22840 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 324 56 81 40 70 134 262), lower := (rows 35 131 324 56 81 40 64 128 256), losses := [] }

theorem u22840 : Upper (D 6) (R 6) [34,129,320,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22840 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22841 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 131 324 56 82 33 76 140 268), lower := (rows 35 131 324 56 82 33 64 128 256), losses := [] }

theorem u22841 : Upper (D 6) (R 6) [34,129,320,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22842 : Route 9 := (fun mask => (mask,id))

def c22842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22842 : Upper (D 6) (R 6) [34,129,320,48,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,48,66,4] 13 (by decide) (choices 1) [1,4,8] r22842 c22842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6993
  · exact u6994
  · exact u6995

def b22843 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 324 56 82 40 69 133 261), lower := (rows 35 131 324 56 82 40 64 128 256), losses := [] }

theorem u22843 : Upper (D 6) (R 6) [34,129,320,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22843 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22844 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 25 82 33 324 452 324), lower := (rows 35 134 44 25 82 33 64 128 256), losses := [] }

theorem u22844 : Upper (D 6) (R 6) [34,132,40,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22845 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 25 82 36 321 449 321), lower := (rows 35 134 44 25 82 36 64 128 256), losses := [] }

theorem u22845 : Upper (D 6) (R 6) [34,132,40,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22846 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 44 25 82 96 325 389 261), lower := (rows 35 134 44 25 82 96 64 128 256), losses := [] }

theorem u22846 : Upper (D 6) (R 6) [34,132,40,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22847 : Route 9 := (fun mask => (mask,id))

def c22847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22847 : Upper (D 6) (R 6) [34,132,40,17,66,256] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17,66,256] 13 (by decide) (choices 1) [1,4] r22847 c22847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6996
  · exact u6997

def b22848 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 25 84 33 322 450 322), lower := (rows 35 134 44 25 84 33 64 128 256), losses := [] }

theorem u22848 : Upper (D 6) (R 6) [34,132,40,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22849 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 25 84 34 321 449 321), lower := (rows 35 134 44 25 84 34 64 128 256), losses := [] }

theorem u22849 : Upper (D 6) (R 6) [34,132,40,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22850 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 44 25 84 96 323 387 259), lower := (rows 35 134 44 25 84 96 64 128 256), losses := [] }

theorem u22850 : Upper (D 6) (R 6) [34,132,40,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22851 : Route 9 := (fun mask => (mask,id))

def c22851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22851 : Upper (D 6) (R 6) [34,132,40,17,68,256] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17,68,256] 13 (by decide) (choices 1) [1,2] r22851 c22851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6998
  · exact u6999

def b22852 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 25 274 33 68 196 324), lower := (rows 35 134 44 25 274 33 64 128 256), losses := [] }

theorem u22852 : Upper (D 6) (R 6) [34,132,40,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22853 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 25 274 36 65 193 321), lower := (rows 35 134 44 25 274 36 64 128 256), losses := [] }

theorem u22853 : Upper (D 6) (R 6) [34,132,40,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22854 : Route 9 := (fun mask => (mask,id))

def c22854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22854 : Upper (D 6) (R 6) [34,132,40,17,258,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17,258,64] 13 (by decide) (choices 1) [1,4] r22854 c22854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7000
  · exact u7001

def b22855 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 25 276 33 66 194 322), lower := (rows 35 134 44 25 276 33 64 128 256), losses := [] }

theorem u22855 : Upper (D 6) (R 6) [34,132,40,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22856 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 25 276 34 65 193 321), lower := (rows 35 134 44 25 276 34 64 128 256), losses := [] }

theorem u22856 : Upper (D 6) (R 6) [34,132,40,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22857 : Route 9 := (fun mask => (mask,id))

def c22857 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22857 : Upper (D 6) (R 6) [34,132,40,17,260,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17,260,64] 13 (by decide) (choices 1) [1,2] r22857 c22857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7002
  · exact u7003

def b22858 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 25 336 33 70 198 326), lower := (rows 35 134 44 25 336 33 64 128 256), losses := [] }

theorem u22858 : Upper (D 6) (R 6) [34,132,40,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22859 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 25 336 34 69 197 325), lower := (rows 35 134 44 25 336 34 64 128 256), losses := [] }

theorem u22859 : Upper (D 6) (R 6) [34,132,40,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22859
end Delivery.IrregularNine14.P06
