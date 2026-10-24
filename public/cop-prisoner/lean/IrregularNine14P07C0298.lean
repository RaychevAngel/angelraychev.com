import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0078

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17880 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 70 200 49 48 195 131 387), lower := (rows 13 290 70 200 49 48 64 128 256), losses := [] }

theorem u17880 : Upper (D 7) (R 7) [12,288,66,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17880 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17881 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 326, targets := 128 }], pairs := [(1,6),(1,7),(2,7),(4,6)], upper := (rows 13 290 70 200 49 160 83 147 275), lower := (rows 13 290 70 200 49 160 64 128 256), losses := [] }

theorem u17881 : Upper (D 7) (R 7) [12,288,66,192,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17882 : Route 9 := (fun mask => (mask,id))

def c17882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17882 : Upper (D 7) (R 7) [12,288,66,192,130,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192,130,1] 13 (by decide) (choices 1) [1,16,32] r17882 c17882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4682
  · exact u4683
  · exact u4684

def r17883 : Route 9 := (fun mask => (mask,id))

def c17883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17883 : Upper (D 7) (R 7) [12,288,66,192,130,16] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192,130,16] 13 (by decide) (choices 1) [1,32] r17883 c17883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4685
  · exact u4686

def r17884 : Route 9 := (fun mask => (mask,id))

def c17884 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17884 : Upper (D 7) (R 7) [12,288,66,192,160,1] 13 := by
  apply FastRouting.sound _ _ [12,288,66,192,160,1] 13 (by decide) (choices 1) [1,2,16] r17884 c17884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4687
  · exact u4688
  · exact u4689

def b17885 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 70 200 176 34 81 145 273), lower := (rows 13 290 70 200 176 34 64 128 256), losses := [] }

theorem u17885 : Upper (D 7) (R 7) [12,288,66,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17886 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 70 200 176 48 67 131 259), lower := (rows 13 290 70 200 176 48 64 128 256), losses := [] }

theorem u17886 : Upper (D 7) (R 7) [12,288,66,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17886 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17887 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 290 84 104 19 33 194 130 386), lower := (rows 13 290 84 104 19 33 64 128 256), losses := [] }

theorem u17887 : Upper (D 7) (R 7) [12,288,80,96,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17888 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 13 290 84 104 19 34 193 129 385), lower := (rows 13 290 84 104 19 34 64 128 256), losses := [] }

theorem u17888 : Upper (D 7) (R 7) [12,288,80,96,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17889 : Route 9 := (fun mask => (mask,id))

def c17889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17889 : Upper (D 7) (R 7) [12,288,80,96,3,128] 13 := by
  apply FastRouting.sound _ _ [12,288,80,96,3,128] 13 (by decide) (choices 1) [1,2,128] r17889 c17889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4690
  · exact u4691
  · exact u4692

def b17890 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 290 84 104 145 33 194 130 386), lower := (rows 13 290 84 104 145 33 64 128 256), losses := [] }

theorem u17890 : Upper (D 7) (R 7) [12,288,80,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17891 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 84 104 145 34 195 131 387), lower := (rows 13 290 84 104 145 34 64 128 256), losses := [] }

theorem u17891 : Upper (D 7) (R 7) [12,288,80,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17892 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(0,1),(1,6),(3,0),(4,6)], upper := (rows 13 290 84 104 145 160 67 131 259), lower := (rows 13 290 84 104 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 176 64 128 256), good := (rows 12 290 124 104 176 160 64 160 256) },{ target := 1, region := (rows 5 0 4 12 16 176 64 128 256), good := (rows 13 288 125 104 177 160 64 160 256) }] }

theorem u17892 : Upper (D 7) (R 7) [12,288,80,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17893 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 290 84 104 146 33 195 131 387), lower := (rows 13 290 84 104 146 33 64 128 256), losses := [] }

theorem u17893 : Upper (D 7) (R 7) [12,288,80,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17894 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 84 104 146 34 193 129 385), lower := (rows 13 290 84 104 146 34 64 128 256), losses := [] }

theorem u17894 : Upper (D 7) (R 7) [12,288,80,96,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17895 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(0,1),(1,6),(3,0),(4,6)], upper := (rows 13 290 84 104 146 160 67 131 259), lower := (rows 13 290 84 104 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 176 64 128 256), good := (rows 12 290 124 104 178 160 64 160 256) },{ target := 1, region := (rows 5 0 4 12 16 176 64 128 256), good := (rows 13 288 125 104 176 160 64 160 256) }] }

theorem u17895 : Upper (D 7) (R 7) [12,288,80,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17896 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 196, targets := 33 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(3,0)], upper := (rows 13 290 84 168 19 33 194 194 450), lower := (rows 13 290 84 168 19 33 64 128 256), losses := [] }

theorem u17896 : Upper (D 7) (R 7) [12,288,80,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17897 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 13 290 84 168 19 34 193 193 449), lower := (rows 13 290 84 168 19 34 64 128 256), losses := [] }

theorem u17897 : Upper (D 7) (R 7) [12,288,80,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17898 : Route 9 := (fun mask => (mask,id))

def c17898 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17898 : Upper (D 7) (R 7) [12,288,80,160,3,64] 13 := by
  apply FastRouting.sound _ _ [12,288,80,160,3,64] 13 (by decide) (choices 1) [1,2,128] r17898 c17898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4693
  · exact u4694
  · exact u4695

def b17899 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 84 168 19 160 67 195 323), lower := (rows 13 290 84 168 19 160 64 128 256), losses := [] }

theorem u17899 : Upper (D 7) (R 7) [12,288,80,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17900 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 40, targets := 66 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,7),(2,7),(3,1),(3,6)], upper := (rows 13 290 84 168 145 33 66 194 322), lower := (rows 13 290 84 168 145 33 64 128 256), losses := [] }

theorem u17900 : Upper (D 7) (R 7) [12,288,80,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17901 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(2,7)], upper := (rows 13 290 84 168 145 34 67 195 323), lower := (rows 13 290 84 168 145 34 64 128 256), losses := [] }

theorem u17901 : Upper (D 7) (R 7) [12,288,80,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17902 : Route 9 := (fun mask => (mask,id))

def c17902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17902 : Upper (D 7) (R 7) [12,288,80,160,129,64] 13 := by
  apply FastRouting.sound _ _ [12,288,80,160,129,64] 13 (by decide) (choices 1) [1,2] r17902 c17902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4696
  · exact u4697

def r17903 : Route 9 := (fun mask => (mask,id))

def c17903 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17903 : Upper (D 7) (R 7) [12,288,80,160,130,1] 13 := by
  apply FastRouting.sound _ _ [12,288,80,160,130,1] 13 (by decide) (choices 1) [1,2] r17903 c17903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4698
  · exact u4699

def b17904 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 290 84 168 146 34 65 193 321), lower := (rows 13 290 84 168 146 34 64 128 256), losses := [] }

theorem u17904 : Upper (D 7) (R 7) [12,288,80,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17905 : Route 9 := (fun mask => (mask,id))

def c17905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17905 : Upper (D 7) (R 7) [12,288,80,160,130,64] 13 := by
  apply FastRouting.sound _ _ [12,288,80,160,130,64] 13 (by decide) (choices 1) [1,2] r17905 c17905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4700
  · exact u4701

def b17906 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(1,6),(3,0),(4,6)], upper := (rows 13 290 84 200 19 33 226 162 418), lower := (rows 13 290 84 200 19 33 64 128 256), losses := [] }

theorem u17906 : Upper (D 7) (R 7) [12,288,80,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17907 : PairBound 9 := { available := 161, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 84 200 19 34 225 161 417), lower := (rows 13 290 84 200 19 34 64 128 256), losses := [] }

theorem u17907 : Upper (D 7) (R 7) [12,288,80,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17908 : Route 9 := (fun mask => (mask,id))

def c17908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17908 : Upper (D 7) (R 7) [12,288,80,192,3,128] 13 := by
  apply FastRouting.sound _ _ [12,288,80,192,3,128] 13 (by decide) (choices 1) [1,2,32] r17908 c17908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4702
  · exact u4703
  · exact u4704

def b17909 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 84 200 49 33 194 130 386), lower := (rows 13 290 84 200 49 33 64 128 256), losses := [] }

theorem u17909 : Upper (D 7) (R 7) [12,288,80,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17910 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 84 200 49 34 195 131 387), lower := (rows 13 290 84 200 49 34 64 128 256), losses := [] }

theorem u17910 : Upper (D 7) (R 7) [12,288,80,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17911 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(4,1)], upper := (rows 13 290 84 200 49 160 67 131 259), lower := (rows 13 290 84 200 49 160 64 128 256), losses := [] }

theorem u17911 : Upper (D 7) (R 7) [12,288,80,192,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17912 : Route 9 := (fun mask => (mask,id))

def c17912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17912 : Upper (D 7) (R 7) [12,288,80,192,130,1] 13 := by
  apply FastRouting.sound _ _ [12,288,80,192,130,1] 13 (by decide) (choices 1) [1,2,32] r17912 c17912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4705
  · exact u4706
  · exact u4707

def b17913 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 84 200 146 34 97 161 289), lower := (rows 13 290 84 200 146 34 64 128 256), losses := [] }

theorem u17913 : Upper (D 7) (R 7) [12,288,80,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17914 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 0, region := 290, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(4,1)], upper := (rows 13 290 84 200 176 33 67 131 259), lower := (rows 13 290 84 200 176 33 64 128 256), losses := [] }

theorem u17914 : Upper (D 7) (R 7) [12,288,80,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17915 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 84 200 176 34 67 131 259), lower := (rows 13 290 84 200 176 34 64 128 256), losses := [] }

theorem u17915 : Upper (D 7) (R 7) [12,288,80,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17916 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 100 200 19 33 210 146 402), lower := (rows 13 290 100 200 19 33 64 128 256), losses := [] }

theorem u17916 : Upper (D 7) (R 7) [12,288,96,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17917 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 13 290 100 200 19 34 209 145 401), lower := (rows 13 290 100 200 19 34 64 128 256), losses := [] }

theorem u17917 : Upper (D 7) (R 7) [12,288,96,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17918 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 200, targets := 32 }], pairs := [(1,6),(3,5),(4,6)], upper := (rows 13 290 100 200 19 48 195 131 387), lower := (rows 13 290 100 200 19 48 64 128 256), losses := [] }

theorem u17918 : Upper (D 7) (R 7) [12,288,96,192,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17918 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17919 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 3, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(4,6)], upper := (rows 13 290 100 200 19 160 83 147 275), lower := (rows 13 290 100 200 19 160 64 128 256), losses := [] }

theorem u17919 : Upper (D 7) (R 7) [12,288,96,192,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17920 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 100 200 146 33 83 147 275), lower := (rows 13 290 100 200 146 33 64 128 256), losses := [] }

theorem u17920 : Upper (D 7) (R 7) [12,288,96,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17921 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 100 200 146 34 81 145 273), lower := (rows 13 290 100 200 146 34 64 128 256), losses := [] }

theorem u17921 : Upper (D 7) (R 7) [12,288,96,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17922 : Route 9 := (fun mask => (mask,id))

def c17922 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17922 : Upper (D 7) (R 7) [12,288,96,192,130,16] 13 := by
  apply FastRouting.sound _ _ [12,288,96,192,130,16] 13 (by decide) (choices 1) [1,2] r17922 c17922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4708
  · exact u4709

def b17923 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 26 148 96 480 416 416), lower := (rows 35 67 13 26 148 96 64 128 256), losses := [] }

theorem u17923 : Upper (D 7) (R 7) [34,65,9,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17924 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 35 67 13 26 148 160 352 480 352), lower := (rows 35 67 13 26 148 160 64 128 256), losses := [] }

theorem u17924 : Upper (D 7) (R 7) [34,65,9,18,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17925 : Route 9 := (fun mask => (mask,id))

def c17925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17925 : Upper (D 7) (R 7) [34,65,9,18,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,18,132,256] 13 (by decide) (choices 1) [32,128] r17925 c17925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4710
  · exact u4711

def b17926 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 26 176 36 448 448 448), lower := (rows 35 67 13 26 176 36 64 128 256), losses := [] }

theorem u17926 : Upper (D 7) (R 7) [34,65,9,18,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17926 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17927 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 26 176 96 452 388 388), lower := (rows 35 67 13 26 176 96 64 128 256), losses := [] }

theorem u17927 : Upper (D 7) (R 7) [34,65,9,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17928 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 26 176 160 324 452 324), lower := (rows 35 67 13 26 176 160 64 128 256), losses := [] }

theorem u17928 : Upper (D 7) (R 7) [34,65,9,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17929 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 67 13 26 176 288 196 196 452), lower := (rows 35 67 13 26 176 288 64 128 256), losses := [] }

theorem u17929 : Upper (D 7) (R 7) [34,65,9,18,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17929 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17930 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 26 276 96 224 160 416), lower := (rows 35 67 13 26 276 96 64 128 256), losses := [] }

theorem u17930 : Upper (D 7) (R 7) [34,65,9,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17931 : Route 9 := (fun mask => (mask,id))

def c17931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17931 : Upper (D 7) (R 7) [34,65,9,18,260,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,18,260,128] 13 (by decide) (choices 1) [32,128] r17931 c17931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4712
  · exact u4713

def b17932 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 26 304 36 192 192 448), lower := (rows 35 67 13 26 304 36 64 128 256), losses := [] }

theorem u17932 : Upper (D 7) (R 7) [34,65,9,18,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17932 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17933 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 26 304 96 196 132 388), lower := (rows 35 67 13 26 304 96 64 128 256), losses := [] }

theorem u17933 : Upper (D 7) (R 7) [34,65,9,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17934 : Route 9 := (fun mask => (mask,id))

def c17934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17934 : Upper (D 7) (R 7) [34,65,9,18,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,18,288,128] 13 (by decide) (choices 1) [4,128] r17934 c17934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4714
  · exact u4715

def b17935 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 26 400 36 224 224 480), lower := (rows 35 67 13 26 400 36 64 128 256), losses := [] }

theorem u17935 : Upper (D 7) (R 7) [34,65,9,18,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17935 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17936 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 26 400 96 228 164 420), lower := (rows 35 67 13 26 400 96 64 128 256), losses := [] }

theorem u17936 : Upper (D 7) (R 7) [34,65,9,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17937 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 496, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 67 13 26 400 160 100 228 356), lower := (rows 35 67 13 26 400 160 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 35 3 13 63 432 160 0 160 256) }] }

theorem u17937 : Upper (D 7) (R 7) [34,65,9,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17938 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 28 146 96 480 416 416), lower := (rows 35 67 13 28 146 96 64 128 256), losses := [] }

theorem u17938 : Upper (D 7) (R 7) [34,65,9,20,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17939 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 35 67 13 28 146 160 352 480 352), lower := (rows 35 67 13 28 146 160 64 128 256), losses := [] }

theorem u17939 : Upper (D 7) (R 7) [34,65,9,20,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17939
end Delivery.IrregularNine14.P07
