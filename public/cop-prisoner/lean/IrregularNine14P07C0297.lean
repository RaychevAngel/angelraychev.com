import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0076
import IrregularNine14P07C0077
import IrregularNine14P07C0078

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17820 : Route 9 := (fun mask => (mask,id))

def c17820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17820 : Upper (D 7) (R 7) [12,288,66,80,129,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80,129,128] 13 (by decide) (choices 1) [1,2,32] r17820 c17820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4603
  · exact u4604
  · exact u4605

def r17821 : Route 9 := (fun mask => (mask,id))

def c17821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17821 : Upper (D 7) (R 7) [12,288,66,80,130,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80,130,1] 13 (by decide) (choices 1) [1,32,128] r17821 c17821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4606
  · exact u4607
  · exact u4608

def r17822 : Route 9 := (fun mask => (mask,id))

def c17822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17822 : Upper (D 7) (R 7) [12,288,66,80,130,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80,130,128] 13 (by decide) (choices 1) [1,32] r17822 c17822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4609
  · exact u4610

def r17823 : Route 9 := (fun mask => (mask,id))

def c17823 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17823 : Upper (D 7) (R 7) [12,288,66,80,160,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80,160,1] 13 (by decide) (choices 1) [1,2,128] r17823 c17823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4611
  · exact u4612
  · exact u4613

def b17824 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 70 88 176 34 193 129 385), lower := (rows 13 290 70 88 176 34 64 128 256), losses := [] }

theorem u17824 : Upper (D 7) (R 7) [12,288,66,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17825 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 70 88 176 160 67 131 259), lower := (rows 13 290 70 88 176 160 64 128 256), losses := [] }

theorem u17825 : Upper (D 7) (R 7) [12,288,66,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17826 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 290 70 104 145 33 210 146 402), lower := (rows 13 290 70 104 145 33 64 128 256), losses := [] }

theorem u17826 : Upper (D 7) (R 7) [12,288,66,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17827 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 70 104 145 34 209 145 401), lower := (rows 13 290 70 104 145 34 64 128 256), losses := [] }

theorem u17827 : Upper (D 7) (R 7) [12,288,66,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17828 : Route 9 := (fun mask => (mask,id))

def c17828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17828 : Upper (D 7) (R 7) [12,288,66,96,129,16] 13 := by
  apply FastRouting.sound _ _ [12,288,66,96,129,16] 13 (by decide) (choices 1) [1,2,128] r17828 c17828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4614
  · exact u4615
  · exact u4616

def r17829 : Route 9 := (fun mask => (mask,id))

def c17829 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17829 : Upper (D 7) (R 7) [12,288,66,96,129,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,96,129,128] 13 (by decide) (choices 1) [1,2,16] r17829 c17829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4617
  · exact u4618
  · exact u4619

def b17830 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 290 70 104 146 33 209 145 401), lower := (rows 13 290 70 104 146 33 64 128 256), losses := [] }

theorem u17830 : Upper (D 7) (R 7) [12,288,66,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17831 : Route 9 := (fun mask => (mask,id))

def c17831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17831 : Upper (D 7) (R 7) [12,288,66,96,130,16] 13 := by
  apply FastRouting.sound _ _ [12,288,66,96,130,16] 13 (by decide) (choices 1) [1,128] r17831 c17831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4620
  · exact u4621

def r17832 : Route 9 := (fun mask => (mask,id))

def c17832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17832 : Upper (D 7) (R 7) [12,288,66,96,130,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,96,130,128] 13 (by decide) (choices 1) [1,16] r17832 c17832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4622
  · exact u4623

def b17833 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 48, targets := 64 }], pairs := [(1,0),(2,0),(3,0),(4,6)], upper := (rows 13 290 70 138 49 33 208 208 464), lower := (rows 13 290 70 138 49 33 64 128 256), losses := [] }

theorem u17833 : Upper (D 7) (R 7) [12,288,66,130,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17834 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 70 138 49 48 193 193 449), lower := (rows 13 290 70 138 49 48 64 128 256), losses := [] }

theorem u17834 : Upper (D 7) (R 7) [12,288,66,130,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17834 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17835 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 394, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,6),(3,6),(4,1),(4,7)], upper := (rows 13 290 70 138 49 96 209 145 401), lower := (rows 13 290 70 138 49 96 64 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 17 100 64 0 256), good := (rows 61 290 102 10 49 96 96 0 256) }] }

theorem u17835 : Upper (D 7) (R 7) [12,288,66,130,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17836 : Route 9 := (fun mask => (mask,id))

def c17836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17836 : Upper (D 7) (R 7) [12,288,66,130,65,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,65,1] 13 (by decide) (choices 1) [16,32,128] r17836 c17836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4624
  · exact u4625
  · exact u4626

def b17837 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,6),(3,6),(4,1)], upper := (rows 13 290 70 138 81 48 225 161 417), lower := (rows 13 290 70 138 81 48 64 128 256), losses := [] }

theorem u17837 : Upper (D 7) (R 7) [12,288,66,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17837 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17838 : Route 9 := (fun mask => (mask,id))

def c17838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17838 : Upper (D 7) (R 7) [12,288,66,130,65,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,65,128] 13 (by decide) (choices 1) [1,16,32] r17838 c17838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4627
  · exact u4628
  · exact u4629

def r17839 : Route 9 := (fun mask => (mask,id))

def c17839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17839 : Upper (D 7) (R 7) [12,288,66,130,96,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,96,1] 13 (by decide) (choices 1) [1,16,128] r17839 c17839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4630
  · exact u4631
  · exact u4632

def b17840 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 70 138 112 48 193 129 385), lower := (rows 13 290 70 138 112 48 64 128 256), losses := [] }

theorem u17840 : Upper (D 7) (R 7) [12,288,66,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17840 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17841 : Route 9 := (fun mask => (mask,id))

def c17841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17841 : Upper (D 7) (R 7) [12,288,66,130,96,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,96,128] 13 (by decide) (choices 1) [1,16] r17841 c17841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4633
  · exact u4634

def r17842 : Route 9 := (fun mask => (mask,id))

def c17842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17842 : Upper (D 7) (R 7) [12,288,66,130,192,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,192,1] 13 (by decide) (choices 1) [1,16,32] r17842 c17842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4635
  · exact u4636
  · exact u4637

def r17843 : Route 9 := (fun mask => (mask,id))

def c17843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17843 : Upper (D 7) (R 7) [12,288,66,130,192,16] 13 := by
  apply FastRouting.sound _ _ [12,288,66,130,192,16] 13 (by decide) (choices 1) [1,32] r17843 c17843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4638
  · exact u4639

def b17844 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 454, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(3,1)], upper := (rows 13 290 70 152 19 33 224 224 480), lower := (rows 13 290 70 152 19 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 54 24 16 32 98 162 290), good := (rows 12 486 454 156 478 486 64 128 256) }] }

theorem u17844 : Upper (D 7) (R 7) [12,288,66,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17845 : Route 9 := (fun mask => (mask,id))

def c17845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17845 : Upper (D 7) (R 7) [12,288,66,144,3,64] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,3,64] 13 (by decide) (choices 1) [1,32,128] r17845 c17845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4640
  · exact u4641
  · exact u4642

def r17846 : Route 9 := (fun mask => (mask,id))

def c17846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17846 : Upper (D 7) (R 7) [12,288,66,144,3,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,3,128] 13 (by decide) (choices 1) [1,32] r17846 c17846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4643
  · exact u4644

def b17847 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 13 290 70 152 49 33 194 194 450), lower := (rows 13 290 70 152 49 33 64 128 256), losses := [] }

theorem u17847 : Upper (D 7) (R 7) [12,288,66,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17848 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 13 290 70 152 49 34 193 193 449), lower := (rows 13 290 70 152 49 34 64 128 256), losses := [] }

theorem u17848 : Upper (D 7) (R 7) [12,288,66,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17849 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6),(3,6),(4,1),(4,7)], upper := (rows 13 290 70 152 49 96 195 131 387), lower := (rows 13 290 70 152 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 100 64 128 256), good := (rows 61 288 100 152 49 96 96 128 256) },{ target := 7, region := (rows 1 2 4 8 17 100 64 0 256), good := (rows 61 290 102 24 49 96 96 0 256) }] }

theorem u17849 : Upper (D 7) (R 7) [12,288,66,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17850 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 326, targets := 128 }], pairs := [(1,7),(2,7),(4,1),(4,6)], upper := (rows 13 290 70 152 49 160 67 195 323), lower := (rows 13 290 70 152 49 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 168 64 128 256), good := (rows 61 288 68 184 49 160 64 160 256) },{ target := 6, region := (rows 1 2 4 8 17 168 0 128 256), good := (rows 61 290 6 184 49 160 0 160 256) }] }

theorem u17850 : Upper (D 7) (R 7) [12,288,66,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17851 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(1,6),(2,0),(3,6)], upper := (rows 13 290 70 152 81 33 226 162 418), lower := (rows 13 290 70 152 81 33 64 128 256), losses := [] }

theorem u17851 : Upper (D 7) (R 7) [12,288,66,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17852 : PairBound 9 := { available := 161, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 13 290 70 152 81 34 225 161 417), lower := (rows 13 290 70 152 81 34 64 128 256), losses := [] }

theorem u17852 : Upper (D 7) (R 7) [12,288,66,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17853 : Route 9 := (fun mask => (mask,id))

def c17853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17853 : Upper (D 7) (R 7) [12,288,66,144,65,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,65,128] 13 (by decide) (choices 1) [1,2,32] r17853 c17853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4645
  · exact u4646
  · exact u4647

def r17854 : Route 9 := (fun mask => (mask,id))

def c17854 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17854 : Upper (D 7) (R 7) [12,288,66,144,96,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,96,1] 13 (by decide) (choices 1) [1,2,128] r17854 c17854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4648
  · exact u4649
  · exact u4650

def b17855 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 70 152 112 34 193 129 385), lower := (rows 13 290 70 152 112 34 64 128 256), losses := [] }

theorem u17855 : Upper (D 7) (R 7) [12,288,66,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17856 : Route 9 := (fun mask => (mask,id))

def c17856 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17856 : Upper (D 7) (R 7) [12,288,66,144,96,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,144,96,128] 13 (by decide) (choices 1) [1,2] r17856 c17856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4651
  · exact u4652

def r17857 : Route 9 := (fun mask => (mask,id))

def c17857 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17857 : Upper (D 7) (R 7) [12,288,66,160,3,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,3,1] 13 (by decide) (choices 1) [16,128] r17857 c17857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4653
  · exact u4654

def r17858 : Route 9 := (fun mask => (mask,id))

def c17858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17858 : Upper (D 7) (R 7) [12,288,66,160,3,16] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,3,16] 13 (by decide) (choices 1) [1,128] r17858 c17858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4655
  · exact u4656

def r17859 : Route 9 := (fun mask => (mask,id))

def c17859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17859 : Upper (D 7) (R 7) [12,288,66,160,3,64] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,3,64] 13 (by decide) (choices 1) [1,16,128] r17859 c17859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4657
  · exact u4658
  · exact u4659

def b17860 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 70 168 19 160 81 209 337), lower := (rows 13 290 70 168 19 160 64 128 256), losses := [] }

theorem u17860 : Upper (D 7) (R 7) [12,288,66,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17861 : Route 9 := (fun mask => (mask,id))

def c17861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17861 : Upper (D 7) (R 7) [12,288,66,160,65,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,65,1] 13 (by decide) (choices 1) [2,16,128] r17861 c17861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4660
  · exact u4661
  · exact u4662

def b17862 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 70 168 81 34 209 145 401), lower := (rows 13 290 70 168 81 34 64 128 256), losses := [] }

theorem u17862 : Upper (D 7) (R 7) [12,288,66,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17863 : Route 9 := (fun mask => (mask,id))

def c17863 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17863 : Upper (D 7) (R 7) [12,288,66,160,65,16] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,65,16] 13 (by decide) (choices 1) [1,2,128] r17863 c17863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4663
  · exact u4664
  · exact u4665

def b17864 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 70 168 81 160 83 147 275), lower := (rows 13 290 70 168 81 160 64 128 256), losses := [] }

theorem u17864 : Upper (D 7) (R 7) [12,288,66,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17865 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 40, targets := 66 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,7),(2,7),(3,1),(3,6)], upper := (rows 13 290 70 168 145 33 82 210 338), lower := (rows 13 290 70 168 145 33 64 128 256), losses := [] }

theorem u17865 : Upper (D 7) (R 7) [12,288,66,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17866 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 70 168 145 34 81 209 337), lower := (rows 13 290 70 168 145 34 64 128 256), losses := [] }

theorem u17866 : Upper (D 7) (R 7) [12,288,66,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17867 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 70 168 145 48 67 195 323), lower := (rows 13 290 70 168 145 48 64 128 256), losses := [] }

theorem u17867 : Upper (D 7) (R 7) [12,288,66,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17867 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17868 : Route 9 := (fun mask => (mask,id))

def c17868 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17868 : Upper (D 7) (R 7) [12,288,66,160,129,64] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,129,64] 13 (by decide) (choices 1) [1,2,16] r17868 c17868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4666
  · exact u4667
  · exact u4668

def r17869 : Route 9 := (fun mask => (mask,id))

def c17869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17869 : Upper (D 7) (R 7) [12,288,66,160,130,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,130,1] 13 (by decide) (choices 1) [1,16] r17869 c17869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4669
  · exact u4670

def b17870 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 70 168 146 48 65 193 321), lower := (rows 13 290 70 168 146 48 64 128 256), losses := [] }

theorem u17870 : Upper (D 7) (R 7) [12,288,66,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17870 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17871 : Route 9 := (fun mask => (mask,id))

def c17871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17871 : Upper (D 7) (R 7) [12,288,66,160,130,64] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,130,64] 13 (by decide) (choices 1) [1,16] r17871 c17871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4671
  · exact u4672

def r17872 : Route 9 := (fun mask => (mask,id))

def c17872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17872 : Upper (D 7) (R 7) [12,288,66,160,192,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,160,192,1] 13 (by decide) (choices 1) [1,2,16] r17872 c17872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4673
  · exact u4674
  · exact u4675

def b17873 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 70 168 208 34 81 145 273), lower := (rows 13 290 70 168 208 34 64 128 256), losses := [] }

theorem u17873 : Upper (D 7) (R 7) [12,288,66,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17874 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 70 168 208 48 67 131 259), lower := (rows 13 290 70 168 208 48 64 128 256), losses := [] }

theorem u17874 : Upper (D 7) (R 7) [12,288,66,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17874 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17875 : Route 9 := (fun mask => (mask,id))

def c17875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17875 : Upper (D 7) (R 7) [12,288,66,192,3,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192,3,1] 13 (by decide) (choices 1) [16,32,128] r17875 c17875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4676
  · exact u4677
  · exact u4678

def b17876 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 232, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 13 290 70 200 19 48 225 161 417), lower := (rows 13 290 70 200 19 48 64 128 256), losses := [] }

theorem u17876 : Upper (D 7) (R 7) [12,288,66,192,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17876 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17877 : Route 9 := (fun mask => (mask,id))

def c17877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17877 : Upper (D 7) (R 7) [12,288,66,192,3,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192,3,128] 13 (by decide) (choices 1) [1,16,32] r17877 c17877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4679
  · exact u4680
  · exact u4681

def b17878 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 48, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 290 70 200 49 33 210 146 402), lower := (rows 13 290 70 200 49 33 64 128 256), losses := [] }

theorem u17878 : Upper (D 7) (R 7) [12,288,66,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17879 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 13 290 70 200 49 34 209 145 401), lower := (rows 13 290 70 200 49 34 64 128 256), losses := [] }

theorem u17879 : Upper (D 7) (R 7) [12,288,66,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17879
end Delivery.IrregularNine14.P07
