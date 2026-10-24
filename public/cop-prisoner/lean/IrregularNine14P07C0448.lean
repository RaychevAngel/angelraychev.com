import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0162
import IrregularNine14P07C0163

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26880 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 69 26 152 33 194 194 450), lower := (rows 37 290 69 26 152 33 64 128 256), losses := [] }

theorem u26880 : Upper (D 7) (R 7) [36,288,65,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26881 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 290 69 26 152 34 193 193 449), lower := (rows 37 290 69 26 152 34 64 128 256), losses := [] }

theorem u26881 : Upper (D 7) (R 7) [36,288,65,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26882 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 69 26 152 96 195 131 387), lower := (rows 37 290 69 26 152 96 64 128 256), losses := [] }

theorem u26882 : Upper (D 7) (R 7) [36,288,65,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26883 : Route 9 := (fun mask => (mask,id))

def c26883 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26883 : Upper (D 7) (R 7) [36,288,65,18,136,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,136,128] 13 (by decide) (choices 1) [1,2] r26883 c26883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9738
  · exact u9739

def b26884 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 69 26 208 33 202 138 394), lower := (rows 37 290 69 26 208 33 64 128 256), losses := [] }

theorem u26884 : Upper (D 7) (R 7) [36,288,65,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26885 : Route 9 := (fun mask => (mask,id))

def c26885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26885 : Upper (D 7) (R 7) [36,288,65,18,192,2] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,192,2] 13 (by decide) (choices 1) [1,8,128] r26885 c26885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9740
  · exact u9741
  · exact u9742

def r26886 : Route 9 := (fun mask => (mask,id))

def c26886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26886 : Upper (D 7) (R 7) [36,288,65,18,192,8] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,192,8] 13 (by decide) (choices 1) [1,2,128] r26886 c26886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9743
  · exact u9744
  · exact u9745

def r26887 : Route 9 := (fun mask => (mask,id))

def c26887 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26887 : Upper (D 7) (R 7) [36,288,65,18,192,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,18,192,128] 13 (by decide) (choices 1) [1,2,8] r26887 c26887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9746
  · exact u9747
  · exact u9748

def b26888 : PairBound 9 := { available := 152, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 37 290 69 74 145 34 216 152 408), lower := (rows 37 290 69 74 145 34 64 128 256), losses := [] }

theorem u26888 : Upper (D 7) (R 7) [36,288,65,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26889 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 69 74 145 40 210 146 402), lower := (rows 37 290 69 74 145 40 64 128 256), losses := [] }

theorem u26889 : Upper (D 7) (R 7) [36,288,65,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26889 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26890 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 1, region := 200, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 290 69 74 145 48 202 138 394), lower := (rows 37 290 69 74 145 48 64 128 256), losses := [] }

theorem u26890 : Upper (D 7) (R 7) [36,288,65,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26890 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26891 : Route 9 := (fun mask => (mask,id))

def c26891 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26891 : Upper (D 7) (R 7) [36,288,65,66,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,66,129,128] 13 (by decide) (choices 1) [2,8,16] r26891 c26891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9749
  · exact u9750
  · exact u9751

def b26892 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 69 74 146 33 216 152 408), lower := (rows 37 290 69 74 146 33 64 128 256), losses := [] }

theorem u26892 : Upper (D 7) (R 7) [36,288,65,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26893 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 69 74 146 40 209 145 401), lower := (rows 37 290 69 74 146 40 64 128 256), losses := [] }

theorem u26893 : Upper (D 7) (R 7) [36,288,65,66,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26893 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26894 : Route 9 := (fun mask => (mask,id))

def c26894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26894 : Upper (D 7) (R 7) [36,288,65,66,130,16] 13 := by
  apply FastRouting.sound _ _ [36,288,65,66,130,16] 13 (by decide) (choices 1) [1,8,128] r26894 c26894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9752
  · exact u9753
  · exact u9754

def r26895 : Route 9 := (fun mask => (mask,id))

def c26895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26895 : Upper (D 7) (R 7) [36,288,65,66,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,66,130,128] 13 (by decide) (choices 1) [1,8,16] r26895 c26895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9755
  · exact u9756
  · exact u9757

def b26896 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 69 74 152 33 210 146 402), lower := (rows 37 290 69 74 152 33 64 128 256), losses := [] }

theorem u26896 : Upper (D 7) (R 7) [36,288,65,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26897 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 37 290 69 74 152 34 209 145 401), lower := (rows 37 290 69 74 152 34 64 128 256), losses := [] }

theorem u26897 : Upper (D 7) (R 7) [36,288,65,66,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26898 : Route 9 := (fun mask => (mask,id))

def c26898 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26898 : Upper (D 7) (R 7) [36,288,65,66,136,16] 13 := by
  apply FastRouting.sound _ _ [36,288,65,66,136,16] 13 (by decide) (choices 1) [1,2,128] r26898 c26898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9758
  · exact u9759
  · exact u9760

def r26899 : Route 9 := (fun mask => (mask,id))

def c26899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26899 : Upper (D 7) (R 7) [36,288,65,66,136,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,66,136,128] 13 (by decide) (choices 1) [1,2,16] r26899 c26899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9761
  · exact u9762
  · exact u9763

def b26900 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 290 69 88 145 34 202 138 394), lower := (rows 37 290 69 88 145 34 64 128 256), losses := [] }

theorem u26900 : Upper (D 7) (R 7) [36,288,65,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26901 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 69 88 145 40 194 130 386), lower := (rows 37 290 69 88 145 40 64 128 256), losses := [] }

theorem u26901 : Upper (D 7) (R 7) [36,288,65,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26901 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26902 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,1),(1,0),(1,6),(3,0)], upper := (rows 37 290 69 88 145 160 74 138 266), lower := (rows 37 290 69 88 145 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 288 69 125 177 160 64 160 256) }] }

theorem u26902 : Upper (D 7) (R 7) [36,288,65,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26903 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 69 88 146 33 202 138 394), lower := (rows 37 290 69 88 146 33 64 128 256), losses := [] }

theorem u26903 : Upper (D 7) (R 7) [36,288,65,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26904 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 37 290 69 88 146 34 201 137 393), lower := (rows 37 290 69 88 146 34 64 128 256), losses := [{ target := 7, region := (rows 9 258 12 8 16 306 64 0 256), good := (rows 37 290 69 125 50 34 64 0 290) }] }

theorem u26904 : Upper (D 7) (R 7) [36,288,65,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26905 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 69 88 146 40 195 131 387), lower := (rows 37 290 69 88 146 40 64 128 256), losses := [] }

theorem u26905 : Upper (D 7) (R 7) [36,288,65,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26905 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26906 : Route 9 := (fun mask => (mask,id))

def c26906 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26906 : Upper (D 7) (R 7) [36,288,65,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,288,65,80,130,128] 13 (by decide) (choices 1) [1,2,8] r26906 c26906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9764
  · exact u9765
  · exact u9766

def b26907 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 69 88 152 33 194 130 386), lower := (rows 37 290 69 88 152 33 64 128 256), losses := [] }

theorem u26907 : Upper (D 7) (R 7) [36,288,65,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26908 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 37 290 69 88 152 34 195 131 387), lower := (rows 37 290 69 88 152 34 64 128 256), losses := [] }

theorem u26908 : Upper (D 7) (R 7) [36,288,65,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26909 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 290 69 88 152 160 67 131 259), lower := (rows 37 290 69 88 152 160 64 128 256), losses := [] }

theorem u26909 : Upper (D 7) (R 7) [36,288,65,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26910 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 290 69 137 146 34 88 216 344), lower := (rows 37 290 69 137 146 34 64 128 256), losses := [] }

theorem u26910 : Upper (D 7) (R 7) [36,288,65,129,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26911 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 290 69 137 146 40 82 210 338), lower := (rows 37 290 69 137 146 40 64 128 256), losses := [] }

theorem u26911 : Upper (D 7) (R 7) [36,288,65,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26911 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26912 : Route 9 := (fun mask => (mask,id))

def c26912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26912 : Upper (D 7) (R 7) [36,288,65,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,288,65,129,130,16] 13 (by decide) (choices 1) [2,8] r26912 c26912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9767
  · exact u9768

def b26913 : PairBound 9 := { available := 26, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 69 137 146 96 90 154 282), lower := (rows 37 290 69 137 146 96 64 128 256), losses := [] }

theorem u26913 : Upper (D 7) (R 7) [36,288,65,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26914 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 290 69 137 208 34 90 154 282), lower := (rows 37 290 69 137 208 34 64 128 256), losses := [] }

theorem u26914 : Upper (D 7) (R 7) [36,288,65,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26915 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 290 69 137 208 40 82 146 274), lower := (rows 37 290 69 137 208 40 64 128 256), losses := [] }

theorem u26915 : Upper (D 7) (R 7) [36,288,65,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26915 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26916 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 290 69 137 208 48 74 138 266), lower := (rows 37 290 69 137 208 48 64 128 256), losses := [] }

theorem u26916 : Upper (D 7) (R 7) [36,288,65,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26916 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26917 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 69 138 208 33 90 154 282), lower := (rows 37 290 69 138 208 33 64 128 256), losses := [] }

theorem u26917 : Upper (D 7) (R 7) [36,288,65,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26918 : Route 9 := (fun mask => (mask,id))

def c26918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26918 : Upper (D 7) (R 7) [36,288,65,130,192,2] 13 := by
  apply FastRouting.sound _ _ [36,288,65,130,192,2] 13 (by decide) (choices 1) [1,8,16] r26918 c26918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9769
  · exact u9770
  · exact u9771

def r26919 : Route 9 := (fun mask => (mask,id))

def c26919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26919 : Upper (D 7) (R 7) [36,288,65,130,192,8] 13 := by
  apply FastRouting.sound _ _ [36,288,65,130,192,8] 13 (by decide) (choices 1) [1,2,16] r26919 c26919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9772
  · exact u9773
  · exact u9774

def b26920 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 69 138 208 48 75 139 267), lower := (rows 37 290 69 138 208 48 64 128 256), losses := [] }

theorem u26920 : Upper (D 7) (R 7) [36,288,65,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26920 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26921 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 290 70 11 88 33 208 144 400), lower := (rows 37 290 70 11 88 33 64 128 256), losses := [] }

theorem u26921 : Upper (D 7) (R 7) [36,288,66,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26922 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 290 70 11 88 48 193 129 385), lower := (rows 37 290 70 11 88 48 64 128 256), losses := [] }

theorem u26922 : Upper (D 7) (R 7) [36,288,66,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26922 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26923 : Route 9 := (fun mask => (mask,id))

def c26923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26923 : Upper (D 7) (R 7) [36,288,66,3,72,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,3,72,128] 13 (by decide) (choices 1) [1,16,128] r26923 c26923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9775
  · exact u9776
  · exact u9777

def b26924 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 290 70 11 145 40 208 208 464), lower := (rows 37 290 70 11 145 40 64 128 256), losses := [] }

theorem u26924 : Upper (D 7) (R 7) [36,288,66,3,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26924 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26925 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 37 290 70 11 145 48 200 200 456), lower := (rows 37 290 70 11 145 48 64 128 256), losses := [] }

theorem u26925 : Upper (D 7) (R 7) [36,288,66,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26925 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26926 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 290 70 11 145 96 216 152 408), lower := (rows 37 290 70 11 145 96 64 128 256), losses := [] }

theorem u26926 : Upper (D 7) (R 7) [36,288,66,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26927 : Route 9 := (fun mask => (mask,id))

def c26927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26927 : Upper (D 7) (R 7) [36,288,66,3,129,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,3,129,128] 13 (by decide) (choices 1) [8,16] r26927 c26927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9778
  · exact u9779

def b26928 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 290 70 11 152 33 208 208 464), lower := (rows 37 290 70 11 152 33 64 128 256), losses := [] }

theorem u26928 : Upper (D 7) (R 7) [36,288,66,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26929 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 208, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 290 70 11 152 48 193 193 449), lower := (rows 37 290 70 11 152 48 64 128 256), losses := [] }

theorem u26929 : Upper (D 7) (R 7) [36,288,66,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26929 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26930 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 290 70 11 152 96 209 145 401), lower := (rows 37 290 70 11 152 96 64 128 256), losses := [] }

theorem u26930 : Upper (D 7) (R 7) [36,288,66,3,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26931 : Route 9 := (fun mask => (mask,id))

def c26931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26931 : Upper (D 7) (R 7) [36,288,66,3,136,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,3,136,128] 13 (by decide) (choices 1) [1,16] r26931 c26931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9780
  · exact u9781

def b26932 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 290 70 11 208 33 216 152 408), lower := (rows 37 290 70 11 208 33 64 128 256), losses := [] }

theorem u26932 : Upper (D 7) (R 7) [36,288,66,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26933 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 290 70 11 208 40 209 145 401), lower := (rows 37 290 70 11 208 40 64 128 256), losses := [] }

theorem u26933 : Upper (D 7) (R 7) [36,288,66,3,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26933 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26934 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,6),(2,5),(3,6)], upper := (rows 37 290 70 11 208 48 201 137 393), lower := (rows 37 290 70 11 208 48 64 128 256), losses := [] }

theorem u26934 : Upper (D 7) (R 7) [36,288,66,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26934 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26935 : Route 9 := (fun mask => (mask,id))

def c26935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26935 : Upper (D 7) (R 7) [36,288,66,3,192,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,3,192,128] 13 (by decide) (choices 1) [1,8,16] r26935 c26935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9782
  · exact u9783
  · exact u9784

def b26936 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 290 70 25 26 33 192 192 448), lower := (rows 37 290 70 25 26 33 64 128 256), losses := [] }

theorem u26936 : Upper (D 7) (R 7) [36,288,66,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26937 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 290 70 25 26 96 193 129 385), lower := (rows 37 290 70 25 26 96 64 128 256), losses := [] }

theorem u26937 : Upper (D 7) (R 7) [36,288,66,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26938 : Route 9 := (fun mask => (mask,id))

def c26938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26938 : Upper (D 7) (R 7) [36,288,66,17,10,128] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17,10,128] 13 (by decide) (choices 1) [1,128] r26938 c26938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9785
  · exact u9786

def b26939 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 290 70 25 88 33 194 130 386), lower := (rows 37 290 70 25 88 33 64 128 256), losses := [] }

theorem u26939 : Upper (D 7) (R 7) [36,288,66,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26939
end Delivery.IrregularNine14.P07
