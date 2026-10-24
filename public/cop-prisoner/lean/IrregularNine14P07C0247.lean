import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0044
import IrregularNine14P07C0045

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14820 : Route 9 := (fun mask => (mask,id))

def c14820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14820 : Upper (D 7) (R 7) [6,264,33,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,17,66,128] 13 (by decide) (choices 1) [32,128] r14820 c14820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2670
  · exact u2671

def b14821 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 25 112 34 192 192 448), lower := (rows 7 266 37 25 112 34 64 128 256), losses := [] }

theorem u14821 : Upper (D 7) (R 7) [6,264,33,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14822 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 266 37 25 112 96 194 130 386), lower := (rows 7 266 37 25 112 96 64 128 256), losses := [] }

theorem u14822 : Upper (D 7) (R 7) [6,264,33,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14823 : Route 9 := (fun mask => (mask,id))

def c14823 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14823 : Upper (D 7) (R 7) [6,264,33,17,96,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,17,96,128] 13 (by decide) (choices 1) [2,128] r14823 c14823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2672
  · exact u2673

def b14824 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 25 208 34 224 224 480), lower := (rows 7 266 37 25 208 34 64 128 256), losses := [] }

theorem u14824 : Upper (D 7) (R 7) [6,264,33,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14825 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,1),(4,0)], upper := (rows 7 266 37 25 208 96 226 162 418), lower := (rows 7 266 37 25 208 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 112 64 128 256), good := (rows 5 268 37 61 240 96 96 128 256) },{ target := 7, region := (rows 3 2 12 8 16 112 64 0 256), good := (rows 7 271 37 61 112 96 96 0 256) }] }

theorem u14825 : Upper (D 7) (R 7) [6,264,33,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14826 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 26 112 33 192 192 448), lower := (rows 7 266 37 26 112 33 64 128 256), losses := [] }

theorem u14826 : Upper (D 7) (R 7) [6,264,33,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14827 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 266 37 26 112 96 193 129 385), lower := (rows 7 266 37 26 112 96 64 128 256), losses := [] }

theorem u14827 : Upper (D 7) (R 7) [6,264,33,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14828 : Route 9 := (fun mask => (mask,id))

def c14828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14828 : Upper (D 7) (R 7) [6,264,33,18,96,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,18,96,128] 13 (by decide) (choices 1) [1,128] r14828 c14828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2674
  · exact u2675

def b14829 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 26 208 33 224 224 480), lower := (rows 7 266 37 26 208 33 64 128 256), losses := [] }

theorem u14829 : Upper (D 7) (R 7) [6,264,33,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14830 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 266 37 26 208 96 225 161 417), lower := (rows 7 266 37 26 208 96 64 128 256), losses := [{ target := 7, region := (rows 11 2 12 8 16 112 64 0 256), good := (rows 7 271 37 63 112 96 96 0 256) }] }

theorem u14830 : Upper (D 7) (R 7) [6,264,33,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14831 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 56 82 33 192 192 448), lower := (rows 7 266 37 56 82 33 64 128 256), losses := [] }

theorem u14831 : Upper (D 7) (R 7) [6,264,33,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14832 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,6)], upper := (rows 7 266 37 56 82 96 193 129 385), lower := (rows 7 266 37 56 82 96 64 128 256), losses := [] }

theorem u14832 : Upper (D 7) (R 7) [6,264,33,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14833 : Route 9 := (fun mask => (mask,id))

def c14833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14833 : Upper (D 7) (R 7) [6,264,33,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,48,66,128] 13 (by decide) (choices 1) [1,128] r14833 c14833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2676
  · exact u2677

def b14834 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 56 208 33 194 194 450), lower := (rows 7 266 37 56 208 33 64 128 256), losses := [] }

theorem u14834 : Upper (D 7) (R 7) [6,264,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14835 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 56 208 34 193 193 449), lower := (rows 7 266 37 56 208 34 64 128 256), losses := [] }

theorem u14835 : Upper (D 7) (R 7) [6,264,33,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14836 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 266 37 56 208 96 195 131 387), lower := (rows 7 266 37 56 208 96 64 128 256), losses := [] }

theorem u14836 : Upper (D 7) (R 7) [6,264,33,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14837 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 73 112 34 208 144 400), lower := (rows 7 266 37 73 112 34 64 128 256), losses := [] }

theorem u14837 : Upper (D 7) (R 7) [6,264,33,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14838 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 52, targets := 130 }], pairs := [(2,1),(2,7),(4,1)], upper := (rows 7 266 37 73 112 48 194 130 386), lower := (rows 7 266 37 73 112 48 64 128 256), losses := [] }

theorem u14838 : Upper (D 7) (R 7) [6,264,33,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14838 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14839 : Route 9 := (fun mask => (mask,id))

def c14839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14839 : Upper (D 7) (R 7) [6,264,33,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,65,96,128] 13 (by decide) (choices 1) [2,16,128] r14839 c14839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2678
  · exact u2679
  · exact u2680

def b14840 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 266 37 73 146 48 224 224 480), lower := (rows 7 266 37 73 146 48 64 128 256), losses := [] }

theorem u14840 : Upper (D 7) (R 7) [6,264,33,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14840 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14841 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 36, targets := 130 }], pairs := [(1,0),(2,1),(2,7),(4,0)], upper := (rows 7 266 37 73 146 96 240 176 432), lower := (rows 7 266 37 73 146 96 64 128 256), losses := [] }

theorem u14841 : Upper (D 7) (R 7) [6,264,33,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14842 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 7 266 37 73 146 160 112 240 368), lower := (rows 7 266 37 73 146 160 64 128 256), losses := [] }

theorem u14842 : Upper (D 7) (R 7) [6,264,33,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14843 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 73 176 34 208 208 464), lower := (rows 7 266 37 73 176 34 64 128 256), losses := [] }

theorem u14843 : Upper (D 7) (R 7) [6,264,33,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14844 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 37 73 176 48 194 194 450), lower := (rows 7 266 37 73 176 48 64 128 256), losses := [] }

theorem u14844 : Upper (D 7) (R 7) [6,264,33,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14844 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14845 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 36, targets := 130 }], pairs := [(1,0),(2,1),(2,7),(4,0)], upper := (rows 7 266 37 73 176 96 210 146 402), lower := (rows 7 266 37 73 176 96 64 128 256), losses := [] }

theorem u14845 : Upper (D 7) (R 7) [6,264,33,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14846 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 37 73 176 160 82 210 338), lower := (rows 7 266 37 73 176 160 64 128 256), losses := [] }

theorem u14846 : Upper (D 7) (R 7) [6,264,33,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14847 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 73 208 34 240 176 432), lower := (rows 7 266 37 73 208 34 64 128 256), losses := [] }

theorem u14847 : Upper (D 7) (R 7) [6,264,33,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14848 : Route 9 := (fun mask => (mask,id))

def c14848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14848 : Upper (D 7) (R 7) [6,264,33,65,192,16] 13 := by
  apply FastRouting.sound _ _ [6,264,33,65,192,16] 13 (by decide) (choices 1) [2,32,128] r14848 c14848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2681
  · exact u2682
  · exact u2683

def r14849 : Route 9 := (fun mask => (mask,id))

def c14849 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14849 : Upper (D 7) (R 7) [6,264,33,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,65,192,128] 13 (by decide) (choices 1) [2,16,32] r14849 c14849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2684
  · exact u2685
  · exact u2686

def b14850 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 74 112 33 208 144 400), lower := (rows 7 266 37 74 112 33 64 128 256), losses := [] }

theorem u14850 : Upper (D 7) (R 7) [6,264,33,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14851 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 37 74 112 48 193 129 385), lower := (rows 7 266 37 74 112 48 64 128 256), losses := [] }

theorem u14851 : Upper (D 7) (R 7) [6,264,33,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14851 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14852 : Route 9 := (fun mask => (mask,id))

def c14852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14852 : Upper (D 7) (R 7) [6,264,33,66,96,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,66,96,128] 13 (by decide) (choices 1) [1,16,128] r14852 c14852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2687
  · exact u2688
  · exact u2689

def b14853 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 74 176 33 208 208 464), lower := (rows 7 266 37 74 176 33 64 128 256), losses := [] }

theorem u14853 : Upper (D 7) (R 7) [6,264,33,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14854 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 37 74 176 48 193 193 449), lower := (rows 7 266 37 74 176 48 64 128 256), losses := [] }

theorem u14854 : Upper (D 7) (R 7) [6,264,33,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14854 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14855 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 266 37 74 176 96 209 145 401), lower := (rows 7 266 37 74 176 96 64 128 256), losses := [] }

theorem u14855 : Upper (D 7) (R 7) [6,264,33,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14856 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 37 74 176 160 81 209 337), lower := (rows 7 266 37 74 176 160 64 128 256), losses := [] }

theorem u14856 : Upper (D 7) (R 7) [6,264,33,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14857 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 74 208 33 240 176 432), lower := (rows 7 266 37 74 208 33 64 128 256), losses := [] }

theorem u14857 : Upper (D 7) (R 7) [6,264,33,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14858 : Route 9 := (fun mask => (mask,id))

def c14858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14858 : Upper (D 7) (R 7) [6,264,33,66,192,16] 13 := by
  apply FastRouting.sound _ _ [6,264,33,66,192,16] 13 (by decide) (choices 1) [1,32,128] r14858 c14858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2690
  · exact u2691
  · exact u2692

def r14859 : Route 9 := (fun mask => (mask,id))

def c14859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14859 : Upper (D 7) (R 7) [6,264,33,66,192,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,66,192,128] 13 (by decide) (choices 1) [1,16,32] r14859 c14859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2693
  · exact u2694
  · exact u2695

def b14860 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 88 145 34 224 224 480), lower := (rows 7 266 37 88 145 34 64 128 256), losses := [] }

theorem u14860 : Upper (D 7) (R 7) [6,264,33,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14861 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 7 266 37 88 145 96 226 162 418), lower := (rows 7 266 37 88 145 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 6 8 16 104 64 0 256), good := (rows 7 303 37 120 17 96 96 0 256) }] }

theorem u14861 : Upper (D 7) (R 7) [6,264,33,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14862 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 36, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(3,0)], upper := (rows 7 266 37 88 145 160 98 226 354), lower := (rows 7 266 37 88 145 160 64 128 256), losses := [] }

theorem u14862 : Upper (D 7) (R 7) [6,264,33,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14863 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 88 146 33 224 224 480), lower := (rows 7 266 37 88 146 33 64 128 256), losses := [] }

theorem u14863 : Upper (D 7) (R 7) [6,264,33,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14864 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(4,6)], upper := (rows 7 266 37 88 146 96 225 161 417), lower := (rows 7 266 37 88 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 17 32 0 132 260), good := (rows 407 266 437 24 146 32 0 128 256) },{ target := 7, region := (rows 19 2 14 8 16 104 64 0 256), good := (rows 7 303 37 125 23 96 96 0 256) }] }

theorem u14864 : Upper (D 7) (R 7) [6,264,33,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14865 : Route 9 := (fun mask => (mask,id))

def c14865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14865 : Upper (D 7) (R 7) [6,264,33,80,130,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,80,130,128] 13 (by decide) (choices 1) [1,32] r14865 c14865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2696
  · exact u2697

def b14866 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 88 176 33 194 194 450), lower := (rows 7 266 37 88 176 33 64 128 256), losses := [] }

theorem u14866 : Upper (D 7) (R 7) [6,264,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14867 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 88 176 34 193 193 449), lower := (rows 7 266 37 88 176 34 64 128 256), losses := [] }

theorem u14867 : Upper (D 7) (R 7) [6,264,33,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14868 : Route 9 := (fun mask => (mask,id))

def c14868 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14868 : Upper (D 7) (R 7) [6,264,33,80,160,64] 13 := by
  apply FastRouting.sound _ _ [6,264,33,80,160,64] 13 (by decide) (choices 1) [1,2,128] r14868 c14868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2698
  · exact u2699
  · exact u2700

def b14869 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 37 88 176 160 67 195 323), lower := (rows 7 266 37 88 176 160 64 128 256), losses := [] }

theorem u14869 : Upper (D 7) (R 7) [6,264,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14870 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 104 81 34 208 144 400), lower := (rows 7 266 37 104 81 34 64 128 256), losses := [] }

theorem u14870 : Upper (D 7) (R 7) [6,264,33,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14871 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 44, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 7 266 37 104 81 48 194 130 386), lower := (rows 7 266 37 104 81 48 64 128 256), losses := [] }

theorem u14871 : Upper (D 7) (R 7) [6,264,33,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14871 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14872 : Route 9 := (fun mask => (mask,id))

def c14872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14872 : Upper (D 7) (R 7) [6,264,33,96,65,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96,65,128] 13 (by decide) (choices 1) [2,16,128] r14872 c14872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2701
  · exact u2702
  · exact u2703

def b14873 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 104 82 33 208 144 400), lower := (rows 7 266 37 104 82 33 64 128 256), losses := [] }

theorem u14873 : Upper (D 7) (R 7) [6,264,33,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14874 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 266 37 104 82 48 193 129 385), lower := (rows 7 266 37 104 82 48 64 128 256), losses := [] }

theorem u14874 : Upper (D 7) (R 7) [6,264,33,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14874 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14875 : Route 9 := (fun mask => (mask,id))

def c14875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14875 : Upper (D 7) (R 7) [6,264,33,96,66,128] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96,66,128] 13 (by decide) (choices 1) [1,16,128] r14875 c14875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2704
  · exact u2705
  · exact u2706

def b14876 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 104 145 34 208 208 464), lower := (rows 7 266 37 104 145 34 64 128 256), losses := [] }

theorem u14876 : Upper (D 7) (R 7) [6,264,33,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14877 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 7 266 37 104 145 48 194 194 450), lower := (rows 7 266 37 104 145 48 64 128 256), losses := [] }

theorem u14877 : Upper (D 7) (R 7) [6,264,33,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14877 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14878 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 266 37 104 145 96 210 146 402), lower := (rows 7 266 37 104 145 96 64 128 256), losses := [] }

theorem u14878 : Upper (D 7) (R 7) [6,264,33,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14879 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 36, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(3,0)], upper := (rows 7 266 37 104 145 160 82 210 338), lower := (rows 7 266 37 104 145 160 64 128 256), losses := [] }

theorem u14879 : Upper (D 7) (R 7) [6,264,33,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14879
end Delivery.IrregularNine14.P07
