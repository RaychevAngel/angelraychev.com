import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0128
import IrregularNine14P06C0129

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24840 : Route 9 := (fun mask => (mask,id))

def c24840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24840 : Upper (D 6) (R 6) [34,192,257,6,65,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,65,4] 13 (by decide) (choices 1) [8,16,32] r24840 c24840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7709
  · exact u7710
  · exact u7711

def b24841 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 261 14 81 40 116 180 308), lower := (rows 35 194 261 14 81 40 64 128 256), losses := [] }

theorem u24841 : Upper (D 6) (R 6) [34,192,257,6,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24841 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24842 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 261 14 81 48 108 172 300), lower := (rows 35 194 261 14 81 48 64 128 256), losses := [] }

theorem u24842 : Upper (D 6) (R 6) [34,192,257,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24842 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24843 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 194 261 14 84 33 120 184 312), lower := (rows 35 194 261 14 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 37 72 136 264), good := (rows 33 192 293 508 116 33 64 128 256) }] }

theorem u24843 : Upper (D 6) (R 6) [34,192,257,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24844 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 261 14 84 40 113 177 305), lower := (rows 35 194 261 14 84 40 64 128 256), losses := [] }

theorem u24844 : Upper (D 6) (R 6) [34,192,257,6,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24844 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24845 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 261 14 84 48 105 169 297), lower := (rows 35 194 261 14 84 48 64 128 256), losses := [] }

theorem u24845 : Upper (D 6) (R 6) [34,192,257,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24845 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24846 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 194 261 14 88 33 116 180 308), lower := (rows 35 194 261 14 88 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 37 72 136 264), good := (rows 33 192 293 508 472 33 64 128 256) }] }

theorem u24846 : Upper (D 6) (R 6) [34,192,257,6,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24847 : Route 9 := (fun mask => (mask,id))

def c24847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24847 : Upper (D 6) (R 6) [34,192,257,6,72,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,72,4] 13 (by decide) (choices 1) [1,16,32] r24847 c24847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7712
  · exact u7713
  · exact u7714

def b24848 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 261 14 88 48 101 165 293), lower := (rows 35 194 261 14 88 48 64 128 256), losses := [] }

theorem u24848 : Upper (D 6) (R 6) [34,192,257,6,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24848 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24849 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 261 14 112 33 92 156 284), lower := (rows 35 194 261 14 112 33 64 128 256), losses := [] }

theorem u24849 : Upper (D 6) (R 6) [34,192,257,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24850 : Route 9 := (fun mask => (mask,id))

def c24850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24850 : Upper (D 6) (R 6) [34,192,257,6,96,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,96,4] 13 (by decide) (choices 1) [1,8,16] r24850 c24850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7715
  · exact u7716
  · exact u7717

def b24851 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 261 14 112 40 85 149 277), lower := (rows 35 194 261 14 112 40 64 128 256), losses := [] }

theorem u24851 : Upper (D 6) (R 6) [34,192,257,6,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24851 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24852 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 261 14 112 48 77 141 269), lower := (rows 35 194 261 14 112 48 64 128 256), losses := [] }

theorem u24852 : Upper (D 6) (R 6) [34,192,257,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24852 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24853 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 25 52 34 76 204 332), lower := (rows 35 194 261 25 52 34 64 128 256), losses := [] }

theorem u24853 : Upper (D 6) (R 6) [34,192,257,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24854 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 194 261 25 52 36 74 202 330), lower := (rows 35 194 261 25 52 36 64 128 256), losses := [] }

theorem u24854 : Upper (D 6) (R 6) [34,192,257,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24855 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 35 194 261 25 52 40 70 198 326), lower := (rows 35 194 261 25 52 40 64 128 256), losses := [] }

theorem u24855 : Upper (D 6) (R 6) [34,192,257,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24855 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24856 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 261 25 52 96 78 142 270), lower := (rows 35 194 261 25 52 96 64 128 256), losses := [] }

theorem u24856 : Upper (D 6) (R 6) [34,192,257,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24857 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 25 84 34 108 172 300), lower := (rows 35 194 261 25 84 34 64 128 256), losses := [] }

theorem u24857 : Upper (D 6) (R 6) [34,192,257,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24858 : Route 9 := (fun mask => (mask,id))

def c24858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24858 : Upper (D 6) (R 6) [34,192,257,17,68,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,17,68,4] 13 (by decide) (choices 1) [2,8,32] r24858 c24858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7718
  · exact u7719
  · exact u7720

def r24859 : Route 9 := (fun mask => (mask,id))

def c24859 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24859 : Upper (D 6) (R 6) [34,192,257,17,68,8] 13 := by
  apply FastRouting.sound _ _ [34,192,257,17,68,8] 13 (by decide) (choices 1) [2,4,32] r24859 c24859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7721
  · exact u7722
  · exact u7723

def b24860 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 25 112 34 76 140 268), lower := (rows 35 194 261 25 112 34 64 128 256), losses := [] }

theorem u24860 : Upper (D 6) (R 6) [34,192,257,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24861 : Route 9 := (fun mask => (mask,id))

def c24861 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24861 : Upper (D 6) (R 6) [34,192,257,17,96,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,17,96,4] 13 (by decide) (choices 1) [2,4,8] r24861 c24861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7724
  · exact u7725
  · exact u7726

def b24862 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 194 261 25 112 40 70 134 262), lower := (rows 35 194 261 25 112 40 64 128 256), losses := [] }

theorem u24862 : Upper (D 6) (R 6) [34,192,257,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24862 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24863 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 194 261 26 28 33 100 228 356), lower := (rows 35 194 261 26 28 33 64 128 256), losses := [] }

theorem u24863 : Upper (D 6) (R 6) [34,192,257,18,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24864 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 194 261 26 28 36 97 225 353), lower := (rows 35 194 261 26 28 36 64 128 256), losses := [] }

theorem u24864 : Upper (D 6) (R 6) [34,192,257,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24865 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 261 26 28 96 101 165 293), lower := (rows 35 194 261 26 28 96 64 128 256), losses := [] }

theorem u24865 : Upper (D 6) (R 6) [34,192,257,18,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24866 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 261 26 52 33 76 204 332), lower := (rows 35 194 261 26 52 33 64 128 256), losses := [] }

theorem u24866 : Upper (D 6) (R 6) [34,192,257,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24867 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 261 26 52 36 73 201 329), lower := (rows 35 194 261 26 52 36 64 128 256), losses := [] }

theorem u24867 : Upper (D 6) (R 6) [34,192,257,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24868 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 261 26 52 40 69 197 325), lower := (rows 35 194 261 26 52 40 64 128 256), losses := [] }

theorem u24868 : Upper (D 6) (R 6) [34,192,257,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24868 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24869 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 261 26 52 96 77 141 269), lower := (rows 35 194 261 26 52 96 64 128 256), losses := [] }

theorem u24869 : Upper (D 6) (R 6) [34,192,257,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24870 : Route 9 := (fun mask => (mask,id))

def c24870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24870 : Upper (D 6) (R 6) [34,192,257,18,65,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,18,65,4] 13 (by decide) (choices 1) [4,8,32] r24870 c24870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7727
  · exact u7728
  · exact u7729

def b24871 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 194 261 26 81 40 100 164 292), lower := (rows 35 194 261 26 81 40 64 128 256), losses := [] }

theorem u24871 : Upper (D 6) (R 6) [34,192,257,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24871 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24872 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 293, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 261 26 84 33 108 172 300), lower := (rows 35 194 261 26 84 33 64 128 256), losses := [] }

theorem u24872 : Upper (D 6) (R 6) [34,192,257,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24873 : Route 9 := (fun mask => (mask,id))

def c24873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24873 : Upper (D 6) (R 6) [34,192,257,18,68,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,18,68,4] 13 (by decide) (choices 1) [1,8,32] r24873 c24873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7730
  · exact u7731
  · exact u7732

def b24874 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 194 261 26 84 40 101 165 293), lower := (rows 35 194 261 26 84 40 64 128 256), losses := [] }

theorem u24874 : Upper (D 6) (R 6) [34,192,257,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24874 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24875 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 194 261 26 112 33 76 140 268), lower := (rows 35 194 261 26 112 33 64 128 256), losses := [] }

theorem u24875 : Upper (D 6) (R 6) [34,192,257,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24876 : Route 9 := (fun mask => (mask,id))

def c24876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24876 : Upper (D 6) (R 6) [34,192,257,18,96,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,18,96,4] 13 (by decide) (choices 1) [1,4,8] r24876 c24876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7733
  · exact u7734
  · exact u7735

def b24877 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 194 261 26 112 40 69 133 261), lower := (rows 35 194 261 26 112 40 64 128 256), losses := [] }

theorem u24877 : Upper (D 6) (R 6) [34,192,257,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24877 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24878 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 194 261 28 56 33 70 198 326), lower := (rows 35 194 261 28 56 33 64 128 256), losses := [] }

theorem u24878 : Upper (D 6) (R 6) [34,192,257,20,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24879 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 28 56 34 69 197 325), lower := (rows 35 194 261 28 56 34 64 128 256), losses := [] }

theorem u24879 : Upper (D 6) (R 6) [34,192,257,20,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24880 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 56, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 261 28 56 36 67 195 323), lower := (rows 35 194 261 28 56 36 64 128 256), losses := [] }

theorem u24880 : Upper (D 6) (R 6) [34,192,257,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24881 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 261 28 56 96 71 135 263), lower := (rows 35 194 261 28 56 96 64 128 256), losses := [] }

theorem u24881 : Upper (D 6) (R 6) [34,192,257,20,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24882 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 28 81 34 108 172 300), lower := (rows 35 194 261 28 81 34 64 128 256), losses := [] }

theorem u24882 : Upper (D 6) (R 6) [34,192,257,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24883 : Route 9 := (fun mask => (mask,id))

def c24883 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24883 : Upper (D 6) (R 6) [34,192,257,20,65,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,20,65,4] 13 (by decide) (choices 1) [2,8,32] r24883 c24883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7736
  · exact u7737
  · exact u7738

def b24884 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 260, targets := 64 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(2,6)], upper := (rows 35 194 261 28 81 40 102 166 294), lower := (rows 35 194 261 28 81 40 64 128 256), losses := [] }

theorem u24884 : Upper (D 6) (R 6) [34,192,257,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24884 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24885 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 261 28 88 33 102 166 294), lower := (rows 35 194 261 28 88 33 64 128 256), losses := [] }

theorem u24885 : Upper (D 6) (R 6) [34,192,257,20,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24886 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 28 88 34 101 165 293), lower := (rows 35 194 261 28 88 34 64 128 256), losses := [] }

theorem u24886 : Upper (D 6) (R 6) [34,192,257,20,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24887 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 261 28 88 36 99 163 291), lower := (rows 35 194 261 28 88 36 64 128 256), losses := [] }

theorem u24887 : Upper (D 6) (R 6) [34,192,257,20,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24888 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,2),(1,0),(4,2)], upper := (rows 35 194 261 28 112 33 78 142 270), lower := (rows 35 194 261 28 112 33 64 128 256), losses := [] }

theorem u24888 : Upper (D 6) (R 6) [34,192,257,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24889 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 28 112 34 77 141 269), lower := (rows 35 194 261 28 112 34 64 128 256), losses := [] }

theorem u24889 : Upper (D 6) (R 6) [34,192,257,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24890 : Route 9 := (fun mask => (mask,id))

def c24890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24890 : Upper (D 6) (R 6) [34,192,257,20,96,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,20,96,4] 13 (by decide) (choices 1) [1,2,8] r24890 c24890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7739
  · exact u7740
  · exact u7741

def b24891 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 261 28 112 40 71 135 263), lower := (rows 35 194 261 28 112 40 64 128 256), losses := [] }

theorem u24891 : Upper (D 6) (R 6) [34,192,257,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24891 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24892 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 44 81 34 92 156 284), lower := (rows 35 194 261 44 81 34 64 128 256), losses := [] }

theorem u24892 : Upper (D 6) (R 6) [34,192,257,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24893 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 261 44 81 36 90 154 282), lower := (rows 35 194 261 44 81 36 64 128 256), losses := [] }

theorem u24893 : Upper (D 6) (R 6) [34,192,257,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24894 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 261 44 81 40 86 150 278), lower := (rows 35 194 261 44 81 40 64 128 256), losses := [] }

theorem u24894 : Upper (D 6) (R 6) [34,192,257,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24894 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24895 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 261 44 81 48 78 142 270), lower := (rows 35 194 261 44 81 48 64 128 256), losses := [] }

theorem u24895 : Upper (D 6) (R 6) [34,192,257,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24895 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24896 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 261 44 84 33 90 154 282), lower := (rows 35 194 261 44 84 33 64 128 256), losses := [] }

theorem u24896 : Upper (D 6) (R 6) [34,192,257,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24897 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 44 84 34 89 153 281), lower := (rows 35 194 261 44 84 34 64 128 256), losses := [] }

theorem u24897 : Upper (D 6) (R 6) [34,192,257,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24898 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 261 44 84 40 83 147 275), lower := (rows 35 194 261 44 84 40 64 128 256), losses := [] }

theorem u24898 : Upper (D 6) (R 6) [34,192,257,36,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24898 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24899 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 261 44 84 48 75 139 267), lower := (rows 35 194 261 44 84 48 64 128 256), losses := [] }

theorem u24899 : Upper (D 6) (R 6) [34,192,257,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24899 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24899
end Delivery.IrregularNine14.P06
