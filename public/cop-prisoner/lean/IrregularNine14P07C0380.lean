import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0117

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22800 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 296 208 160 67 131 259), lower := (rows 37 74 21 296 208 160 64 128 256), losses := [] }

theorem u22800 : Upper (D 7) (R 7) [36,72,17,288,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22801 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 392 146 33 98 226 354), lower := (rows 37 74 21 392 146 33 64 128 256), losses := [] }

theorem u22801 : Upper (D 7) (R 7) [36,72,17,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22802 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 37, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 392 146 34 97 225 353), lower := (rows 37 74 21 392 146 34 64 128 256), losses := [] }

theorem u22802 : Upper (D 7) (R 7) [36,72,17,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22803 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 101, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 21 392 146 96 99 163 291), lower := (rows 37 74 21 392 146 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 8 16 98 64 128 256), good := (rows 37 104 21 392 181 96 96 128 256) }] }

theorem u22803 : Upper (D 7) (R 7) [36,72,17,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22804 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 392 208 33 98 162 290), lower := (rows 37 74 21 392 208 33 64 128 256), losses := [] }

theorem u22804 : Upper (D 7) (R 7) [36,72,17,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22805 : Route 9 := (fun mask => (mask,id))

def c22805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22805 : Upper (D 7) (R 7) [36,72,17,384,192,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,384,192,2] 13 (by decide) (choices 1) [1,2,32] r22805 c22805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7024
  · exact u7025
  · exact u7026

def b22806 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 74 22 42 145 33 448 448 448), lower := (rows 37 74 22 42 145 33 64 128 256), losses := [] }

theorem u22806 : Upper (D 7) (R 7) [36,72,18,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22807 : PairBound 9 := { available := 385, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 22 42 145 96 449 385 385), lower := (rows 37 74 22 42 145 96 64 128 256), losses := [] }

theorem u22807 : Upper (D 7) (R 7) [36,72,18,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22808 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 74 22 42 145 160 321 449 321), lower := (rows 37 74 22 42 145 160 64 128 256), losses := [] }

theorem u22808 : Upper (D 7) (R 7) [36,72,18,34,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22809 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,1),(4,1),(4,5)], upper := (rows 37 74 22 42 145 288 193 193 449), lower := (rows 37 74 22 42 145 288 64 128 256), losses := [] }

theorem u22809 : Upper (D 7) (R 7) [36,72,18,34,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22809 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22810 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 74 22 42 273 33 192 192 448), lower := (rows 37 74 22 42 273 33 64 128 256), losses := [] }

theorem u22810 : Upper (D 7) (R 7) [36,72,18,34,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22811 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 22 42 273 96 193 129 385), lower := (rows 37 74 22 42 273 96 64 128 256), losses := [] }

theorem u22811 : Upper (D 7) (R 7) [36,72,18,34,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22812 : Route 9 := (fun mask => (mask,id))

def c22812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22812 : Upper (D 7) (R 7) [36,72,18,34,257,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,34,257,128] 13 (by decide) (choices 1) [1,128] r22812 c22812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7027
  · exact u7028

def b22813 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 74 22 42 400 33 193 193 449), lower := (rows 37 74 22 42 400 33 64 128 256), losses := [] }

theorem u22813 : Upper (D 7) (R 7) [36,72,18,34,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22814 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 22 42 400 96 193 129 385), lower := (rows 37 74 22 42 400 96 64 128 256), losses := [] }

theorem u22814 : Upper (D 7) (R 7) [36,72,18,34,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22815 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 74 22 42 400 160 65 193 321), lower := (rows 37 74 22 42 400 160 64 128 256), losses := [] }

theorem u22815 : Upper (D 7) (R 7) [36,72,18,34,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22816 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 392, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(4,7)], upper := (rows 37 74 22 137 81 34 480 416 416), lower := (rows 37 74 22 137 81 34 64 128 256), losses := [] }

theorem u22816 : Upper (D 7) (R 7) [36,72,18,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22817 : Route 9 := (fun mask => (mask,id))

def c22817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u22817 : Upper (D 7) (R 7) [36,72,18,129,65,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,65,128] 13 (by decide) (choices 1) [2,32,256] r22817 c22817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7029
  · exact u7030
  · exact u7031

def b22818 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 3, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 37 74 22 137 81 288 226 162 418), lower := (rows 37 74 22 137 81 288 64 128 256), losses := [] }

theorem u22818 : Upper (D 7) (R 7) [36,72,18,129,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22818 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22819 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 22 137 273 34 224 224 480), lower := (rows 37 74 22 137 273 34 64 128 256), losses := [] }

theorem u22819 : Upper (D 7) (R 7) [36,72,18,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22820 : Route 9 := (fun mask => (mask,id))

def c22820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22820 : Upper (D 7) (R 7) [36,72,18,129,257,64] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,257,64] 13 (by decide) (choices 1) [2,32,128] r22820 c22820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7032
  · exact u7033
  · exact u7034

def r22821 : Route 9 := (fun mask => (mask,id))

def c22821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22821 : Upper (D 7) (R 7) [36,72,18,129,257,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,257,128] 13 (by decide) (choices 1) [2,32] r22821 c22821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7035
  · exact u7036

def b22822 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 202, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 22 137 304 33 194 194 450), lower := (rows 37 74 22 137 304 33 64 128 256), losses := [] }

theorem u22822 : Upper (D 7) (R 7) [36,72,18,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22823 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5),(3,1),(3,5),(4,1)], upper := (rows 37 74 22 137 304 34 193 193 449), lower := (rows 37 74 22 137 304 34 64 128 256), losses := [] }

theorem u22823 : Upper (D 7) (R 7) [36,72,18,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22824 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(3,5)], upper := (rows 37 74 22 137 304 96 195 131 387), lower := (rows 37 74 22 137 304 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 104 53 137 304 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 16 98 64 0 256), good := (rows 37 106 55 9 304 96 96 0 256) }] }

theorem u22824 : Upper (D 7) (R 7) [36,72,18,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22825 : Route 9 := (fun mask => (mask,id))

def c22825 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22825 : Upper (D 7) (R 7) [36,72,18,129,288,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,288,128] 13 (by decide) (choices 1) [1,2] r22825 c22825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7037
  · exact u7038

def b22826 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 74 22 137 336 33 226 162 418), lower := (rows 37 74 22 137 336 33 64 128 256), losses := [] }

theorem u22826 : Upper (D 7) (R 7) [36,72,18,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22827 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 22 137 336 34 225 161 417), lower := (rows 37 74 22 137 336 34 64 128 256), losses := [] }

theorem u22827 : Upper (D 7) (R 7) [36,72,18,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22828 : Route 9 := (fun mask => (mask,id))

def c22828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22828 : Upper (D 7) (R 7) [36,72,18,129,320,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,320,128] 13 (by decide) (choices 1) [1,2,32] r22828 c22828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7039
  · exact u7040
  · exact u7041

def b22829 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 33, targets := 128 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 74 22 137 400 33 98 226 354), lower := (rows 37 74 22 137 400 33 64 128 256), losses := [] }

theorem u22829 : Upper (D 7) (R 7) [36,72,18,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22830 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 22 137 400 34 97 225 353), lower := (rows 37 74 22 137 400 34 64 128 256), losses := [] }

theorem u22830 : Upper (D 7) (R 7) [36,72,18,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22831 : Route 9 := (fun mask => (mask,id))

def c22831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22831 : Upper (D 7) (R 7) [36,72,18,129,384,64] 13 := by
  apply FastRouting.sound _ _ [36,72,18,129,384,64] 13 (by decide) (choices 1) [1,2,32] r22831 c22831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7042
  · exact u7043
  · exact u7044

def b22832 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 22 138 145 33 352 480 352), lower := (rows 37 74 22 138 145 33 64 128 256), losses := [] }

theorem u22832 : Upper (D 7) (R 7) [36,72,18,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22833 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 0, region := 400, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,1),(0,7),(4,1),(4,6)], upper := (rows 37 74 22 138 145 96 353 417 289), lower := (rows 37 74 22 138 145 96 64 128 256), losses := [] }

theorem u22833 : Upper (D 7) (R 7) [36,72,18,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22834 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 74 22 138 145 288 97 225 353), lower := (rows 37 74 22 138 145 288 64 128 256), losses := [] }

theorem u22834 : Upper (D 7) (R 7) [36,72,18,130,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22834 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22835 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 74 22 138 273 33 224 224 480), lower := (rows 37 74 22 138 273 33 64 128 256), losses := [] }

theorem u22835 : Upper (D 7) (R 7) [36,72,18,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22836 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,1),(0,7),(4,1),(4,6)], upper := (rows 37 74 22 138 273 96 225 161 417), lower := (rows 37 74 22 138 273 96 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 98 64 0 256), good := (rows 37 106 55 42 273 96 96 0 256) }] }

theorem u22836 : Upper (D 7) (R 7) [36,72,18,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22837 : Route 9 := (fun mask => (mask,id))

def c22837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22837 : Upper (D 7) (R 7) [36,72,18,130,257,128] 13 := by
  apply FastRouting.sound _ _ [36,72,18,130,257,128] 13 (by decide) (choices 1) [1,32] r22837 c22837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7045
  · exact u7046

def b22838 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 74 22 138 400 33 97 225 353), lower := (rows 37 74 22 138 400 33 64 128 256), losses := [] }

theorem u22838 : Upper (D 7) (R 7) [36,72,18,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22839 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 0, region := 400, targets := 64 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(4,1),(4,6)], upper := (rows 37 74 22 138 400 96 97 161 289), lower := (rows 37 74 22 138 400 96 64 128 256), losses := [] }

theorem u22839 : Upper (D 7) (R 7) [36,72,18,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22840 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 22 168 81 33 450 386 386), lower := (rows 37 74 22 168 81 33 64 128 256), losses := [] }

theorem u22840 : Upper (D 7) (R 7) [36,72,18,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22841 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 392, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(4,7)], upper := (rows 37 74 22 168 81 34 449 385 385), lower := (rows 37 74 22 168 81 34 64 128 256), losses := [] }

theorem u22841 : Upper (D 7) (R 7) [36,72,18,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22842 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 22 168 81 160 323 387 259), lower := (rows 37 74 22 168 81 160 64 128 256), losses := [] }

theorem u22842 : Upper (D 7) (R 7) [36,72,18,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22843 : Route 9 := (fun mask => (mask,id))

def c22843 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22843 : Upper (D 7) (R 7) [36,72,18,160,65,256] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,65,256] 13 (by decide) (choices 1) [1,2,128] r22843 c22843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7047
  · exact u7048
  · exact u7049

def b22844 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(3,0)], upper := (rows 37 74 22 168 145 33 322 450 322), lower := (rows 37 74 22 168 145 33 64 128 256), losses := [] }

theorem u22844 : Upper (D 7) (R 7) [36,72,18,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22845 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,5)], upper := (rows 37 74 22 168 145 34 321 449 321), lower := (rows 37 74 22 168 145 34 64 128 256), losses := [] }

theorem u22845 : Upper (D 7) (R 7) [36,72,18,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22846 : Route 9 := (fun mask => (mask,id))

def c22846 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u22846 : Upper (D 7) (R 7) [36,72,18,160,129,64] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,129,64] 13 (by decide) (choices 1) [1,2,256] r22846 c22846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7050
  · exact u7051
  · exact u7052

def r22847 : Route 9 := (fun mask => (mask,id))

def c22847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22847 : Upper (D 7) (R 7) [36,72,18,160,129,256] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,129,256] 13 (by decide) (choices 1) [1,2] r22847 c22847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7053
  · exact u7054

def b22848 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 2, region := 33, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 74 22 168 208 33 323 387 259), lower := (rows 37 74 22 168 208 33 64 128 256), losses := [] }

theorem u22848 : Upper (D 7) (R 7) [36,72,18,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22849 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 46, targets := 1 },{ cop := 0, region := 392, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(3,1)], upper := (rows 37 74 22 168 208 34 321 385 257), lower := (rows 37 74 22 168 208 34 64 128 256), losses := [] }

theorem u22849 : Upper (D 7) (R 7) [36,72,18,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22850 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 2, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 74 22 168 208 288 67 131 259), lower := (rows 37 74 22 168 208 288 64 128 256), losses := [] }

theorem u22850 : Upper (D 7) (R 7) [36,72,18,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22850 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22851 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 202, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 22 168 273 33 194 194 450), lower := (rows 37 74 22 168 273 33 64 128 256), losses := [] }

theorem u22851 : Upper (D 7) (R 7) [36,72,18,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22852 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 22 168 273 34 193 193 449), lower := (rows 37 74 22 168 273 34 64 128 256), losses := [] }

theorem u22852 : Upper (D 7) (R 7) [36,72,18,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22853 : Route 9 := (fun mask => (mask,id))

def c22853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22853 : Upper (D 7) (R 7) [36,72,18,160,257,64] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,257,64] 13 (by decide) (choices 1) [1,2,128] r22853 c22853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7055
  · exact u7056
  · exact u7057

def b22854 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 22 168 273 160 67 195 323), lower := (rows 37 74 22 168 273 160 64 128 256), losses := [] }

theorem u22854 : Upper (D 7) (R 7) [36,72,18,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22855 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 74 22 168 336 33 195 131 387), lower := (rows 37 74 22 168 336 33 64 128 256), losses := [] }

theorem u22855 : Upper (D 7) (R 7) [36,72,18,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22856 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 22 168 336 34 193 129 385), lower := (rows 37 74 22 168 336 34 64 128 256), losses := [] }

theorem u22856 : Upper (D 7) (R 7) [36,72,18,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22857 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 22 168 336 160 67 131 259), lower := (rows 37 74 22 168 336 160 64 128 256), losses := [] }

theorem u22857 : Upper (D 7) (R 7) [36,72,18,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22858 : Route 9 := (fun mask => (mask,id))

def c22858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22858 : Upper (D 7) (R 7) [36,72,18,160,384,1] 13 := by
  apply FastRouting.sound _ _ [36,72,18,160,384,1] 13 (by decide) (choices 1) [1,2] r22858 c22858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7058
  · exact u7059

def b22859 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,5)], upper := (rows 37 74 22 168 400 34 65 193 321), lower := (rows 37 74 22 168 400 34 64 128 256), losses := [] }

theorem u22859 : Upper (D 7) (R 7) [36,72,18,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22859
end Delivery.IrregularNine14.P07
