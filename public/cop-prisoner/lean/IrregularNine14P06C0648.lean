import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0416
import IrregularNine14P06C0417
import IrregularNine14P06C0418

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38880 : Route 9 := (fun mask => (mask,id))

def c38880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38880 : Upper (D 6) (R 6) [34,192,264,6,96] 13 := by
  apply FastRouting.sound _ _ [34,192,264,6,96] 13 (by decide) (choices 1) [1,4,16] r38880 c38880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25002
  · exact u25003
  · exact u25004

def b38881 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 268 25 19 100 100 228 356), lower := (rows 35 194 268 25 19 32 64 128 256), losses := [] }

theorem u38881 : Upper (D 6) (R 6) [34,192,264,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38882 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 268 25 21 102 102 230 358), lower := (rows 35 194 268 25 21 32 64 128 256), losses := [] }

theorem u38882 : Upper (D 6) (R 6) [34,192,264,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38883 : Route 9 := (fun mask => (mask,id))

def c38883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38883 : Upper (D 6) (R 6) [34,192,264,17,6] 13 := by
  apply FastRouting.sound _ _ [34,192,264,17,6] 13 (by decide) (choices 1) [1,4,64] r38883 c38883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25005
  · exact u25006
  · exact u25007

def b38884 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 268 25 49 102 70 198 326), lower := (rows 35 194 268 25 49 32 64 128 256), losses := [] }

theorem u38884 : Upper (D 6) (R 6) [34,192,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38885 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 268 25 50 101 69 197 325), lower := (rows 35 194 268 25 50 32 64 128 256), losses := [] }

theorem u38885 : Upper (D 6) (R 6) [34,192,264,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38886 : Route 9 := (fun mask => (mask,id))

def c38886 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38886 : Upper (D 6) (R 6) [34,192,264,17,36] 13 := by
  apply FastRouting.sound _ _ [34,192,264,17,36] 13 (by decide) (choices 1) [1,2,4,64] r38886 c38886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25008
  · exact u25009
  · exact u25010
  · exact u25011

def b38887 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 268 25 81 38 102 166 294), lower := (rows 35 194 268 25 81 32 64 128 256), losses := [] }

theorem u38887 : Upper (D 6) (R 6) [34,192,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38888 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 268 25 82 37 101 165 293), lower := (rows 35 194 268 25 82 32 64 128 256), losses := [] }

theorem u38888 : Upper (D 6) (R 6) [34,192,264,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38889 : Route 9 := (fun mask => (mask,id))

def c38889 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38889 : Upper (D 6) (R 6) [34,192,264,17,68] 13 := by
  apply FastRouting.sound _ _ [34,192,264,17,68] 13 (by decide) (choices 1) [1,2,4] r38889 c38889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25012
  · exact u25013
  · exact u25014

def r38890 : Route 9 := (fun mask => (mask,id))

def c38890 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38890 : Upper (D 6) (R 6) [34,192,264,17,96] 13 := by
  apply FastRouting.sound _ _ [34,192,264,17,96] 13 (by decide) (choices 1) [1,2,4] r38890 c38890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25015
  · exact u25016
  · exact u25017

def r38891 : Route 9 := (fun mask => (mask,id))

def c38891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38891 : Upper (D 6) (R 6) [34,192,264,18,5] 13 := by
  apply FastRouting.sound _ _ [34,192,264,18,5] 13 (by decide) (choices 1) [1,4,64] r38891 c38891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25018
  · exact u25019
  · exact u25020

def b38892 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 268 26 49 101 69 197 325), lower := (rows 35 194 268 26 49 32 64 128 256), losses := [] }

theorem u38892 : Upper (D 6) (R 6) [34,192,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38893 : Route 9 := (fun mask => (mask,id))

def c38893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38893 : Upper (D 6) (R 6) [34,192,264,18,36] 13 := by
  apply FastRouting.sound _ _ [34,192,264,18,36] 13 (by decide) (choices 1) [1,4,64] r38893 c38893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25021
  · exact u25022
  · exact u25023

def r38894 : Route 9 := (fun mask => (mask,id))

def c38894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38894 : Upper (D 6) (R 6) [34,192,264,18,65] 13 := by
  apply FastRouting.sound _ _ [34,192,264,18,65] 13 (by decide) (choices 1) [1,4] r38894 c38894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25024
  · exact u25025

def r38895 : Route 9 := (fun mask => (mask,id))

def c38895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38895 : Upper (D 6) (R 6) [34,192,264,18,68] 13 := by
  apply FastRouting.sound _ _ [34,192,264,18,68] 13 (by decide) (choices 1) [1,4] r38895 c38895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25026
  · exact u25027

def r38896 : Route 9 := (fun mask => (mask,id))

def c38896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38896 : Upper (D 6) (R 6) [34,192,264,18,96] 13 := by
  apply FastRouting.sound _ _ [34,192,264,18,96] 13 (by decide) (choices 1) [1,4] r38896 c38896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25028
  · exact u25029

def b38897 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 268 28 19 101 101 229 357), lower := (rows 35 194 268 28 19 32 64 128 256), losses := [] }

theorem u38897 : Upper (D 6) (R 6) [34,192,264,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38898 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 268 28 21 99 99 227 355), lower := (rows 35 194 268 28 21 32 64 128 256), losses := [] }

theorem u38898 : Upper (D 6) (R 6) [34,192,264,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38899 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 268 28 22 97 97 225 353), lower := (rows 35 194 268 28 22 32 64 128 256), losses := [] }

theorem u38899 : Upper (D 6) (R 6) [34,192,264,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38900 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 268 28 49 103 71 199 327), lower := (rows 35 194 268 28 49 32 64 128 256), losses := [] }

theorem u38900 : Upper (D 6) (R 6) [34,192,264,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38901 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 268 28 50 101 69 197 325), lower := (rows 35 194 268 28 50 32 64 128 256), losses := [] }

theorem u38901 : Upper (D 6) (R 6) [34,192,264,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38902 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 268 28 52 99 67 195 323), lower := (rows 35 194 268 28 52 32 64 128 256), losses := [] }

theorem u38902 : Upper (D 6) (R 6) [34,192,264,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38903 : Route 9 := (fun mask => (mask,id))

def c38903 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38903 : Upper (D 6) (R 6) [34,192,264,20,65] 13 := by
  apply FastRouting.sound _ _ [34,192,264,20,65] 13 (by decide) (choices 1) [1,2,4] r38903 c38903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25030
  · exact u25031
  · exact u25032

def b38904 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 268 28 82 37 101 165 293), lower := (rows 35 194 268 28 82 32 64 128 256), losses := [] }

theorem u38904 : Upper (D 6) (R 6) [34,192,264,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38905 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 268 28 84 35 99 163 291), lower := (rows 35 194 268 28 84 32 64 128 256), losses := [] }

theorem u38905 : Upper (D 6) (R 6) [34,192,264,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38906 : Route 9 := (fun mask => (mask,id))

def c38906 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38906 : Upper (D 6) (R 6) [34,192,264,20,96] 13 := by
  apply FastRouting.sound _ _ [34,192,264,20,96] 13 (by decide) (choices 1) [1,2,4] r38906 c38906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25033
  · exact u25034
  · exact u25035

def b38907 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 268 44 19 117 85 213 341), lower := (rows 35 194 268 44 19 32 64 128 256), losses := [] }

theorem u38907 : Upper (D 6) (R 6) [34,192,264,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38908 : PairBound 9 := { available := 83, camps := [{ cop := 4, region := 227, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 194 268 44 21 115 83 211 339), lower := (rows 35 194 268 44 21 32 64 128 256), losses := [] }

theorem u38908 : Upper (D 6) (R 6) [34,192,264,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38909 : Route 9 := (fun mask => (mask,id))

def c38909 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38909 : Upper (D 6) (R 6) [34,192,264,36,6] 13 := by
  apply FastRouting.sound _ _ [34,192,264,36,6] 13 (by decide) (choices 1) [1,16,64] r38909 c38909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25036
  · exact u25037
  · exact u25038

def r38910 : Route 9 := (fun mask => (mask,id))

def c38910 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38910 : Upper (D 6) (R 6) [34,192,264,36,65] 13 := by
  apply FastRouting.sound _ _ [34,192,264,36,65] 13 (by decide) (choices 1) [1,2,4,16] r38910 c38910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25039
  · exact u25040
  · exact u25041
  · exact u25042

def b38911 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 268 44 82 53 85 149 277), lower := (rows 35 194 268 44 82 32 64 128 256), losses := [] }

theorem u38911 : Upper (D 6) (R 6) [34,192,264,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38912 : Route 9 := (fun mask => (mask,id))

def c38912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38912 : Upper (D 6) (R 6) [34,192,264,36,68] 13 := by
  apply FastRouting.sound _ _ [34,192,264,36,68] 13 (by decide) (choices 1) [1,2,16] r38912 c38912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25043
  · exact u25044
  · exact u25045

def b38913 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 268 56 19 101 69 197 325), lower := (rows 35 194 268 56 19 32 64 128 256), losses := [] }

theorem u38913 : Upper (D 6) (R 6) [34,192,264,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38914 : Route 9 := (fun mask => (mask,id))

def c38914 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38914 : Upper (D 6) (R 6) [34,192,264,48,5] 13 := by
  apply FastRouting.sound _ _ [34,192,264,48,5] 13 (by decide) (choices 1) [1,2,4,64] r38914 c38914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25046
  · exact u25047
  · exact u25048
  · exact u25049

def r38915 : Route 9 := (fun mask => (mask,id))

def c38915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38915 : Upper (D 6) (R 6) [34,192,264,48,6] 13 := by
  apply FastRouting.sound _ _ [34,192,264,48,6] 13 (by decide) (choices 1) [1,4,64] r38915 c38915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25050
  · exact u25051
  · exact u25052

def r38916 : Route 9 := (fun mask => (mask,id))

def c38916 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38916 : Upper (D 6) (R 6) [34,192,264,48,65] 13 := by
  apply FastRouting.sound _ _ [34,192,264,48,65] 13 (by decide) (choices 1) [1,2,4] r38916 c38916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25053
  · exact u25054
  · exact u25055

def b38917 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 268 56 82 37 69 133 261), lower := (rows 35 194 268 56 82 32 64 128 256), losses := [] }

theorem u38917 : Upper (D 6) (R 6) [34,192,264,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38918 : Route 9 := (fun mask => (mask,id))

def c38918 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38918 : Upper (D 6) (R 6) [34,192,264,48,68] 13 := by
  apply FastRouting.sound _ _ [34,192,264,48,68] 13 (by decide) (choices 1) [1,2,4] r38918 c38918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25056
  · exact u25057
  · exact u25058

def b38919 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 268 73 19 52 116 180 308), lower := (rows 35 194 268 73 19 32 64 128 256), losses := [] }

theorem u38919 : Upper (D 6) (R 6) [34,192,264,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38920 : Route 9 := (fun mask => (mask,id))

def c38920 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38920 : Upper (D 6) (R 6) [34,192,264,65,5] 13 := by
  apply FastRouting.sound _ _ [34,192,264,65,5] 13 (by decide) (choices 1) [2,4,16] r38920 c38920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25059
  · exact u25060
  · exact u25061

def r38921 : Route 9 := (fun mask => (mask,id))

def c38921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38921 : Upper (D 6) (R 6) [34,192,264,65,6] 13 := by
  apply FastRouting.sound _ _ [34,192,264,65,6] 13 (by decide) (choices 1) [1,4,16] r38921 c38921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25062
  · exact u25063
  · exact u25064

def b38922 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 268 73 49 54 86 150 278), lower := (rows 35 194 268 73 49 32 64 128 256), losses := [] }

theorem u38922 : Upper (D 6) (R 6) [34,192,264,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38923 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 268 73 50 53 85 149 277), lower := (rows 35 194 268 73 50 32 64 128 256), losses := [] }

theorem u38923 : Upper (D 6) (R 6) [34,192,264,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38924 : Route 9 := (fun mask => (mask,id))

def c38924 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38924 : Upper (D 6) (R 6) [34,192,264,65,36] 13 := by
  apply FastRouting.sound _ _ [34,192,264,65,36] 13 (by decide) (choices 1) [1,2,4,16] r38924 c38924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25065
  · exact u25066
  · exact u25067
  · exact u25068

def b38925 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 268 76 19 53 117 181 309), lower := (rows 35 194 268 76 19 32 64 128 256), losses := [] }

theorem u38925 : Upper (D 6) (R 6) [34,192,264,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38926 : Route 9 := (fun mask => (mask,id))

def c38926 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38926 : Upper (D 6) (R 6) [34,192,264,68,5] 13 := by
  apply FastRouting.sound _ _ [34,192,264,68,5] 13 (by decide) (choices 1) [1,2,16] r38926 c38926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25069
  · exact u25070
  · exact u25071

def b38927 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 227, targets := 4 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 268 76 22 49 113 177 305), lower := (rows 35 194 268 76 22 32 64 128 256), losses := [] }

theorem u38927 : Upper (D 6) (R 6) [34,192,264,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38928 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 268 76 49 55 87 151 279), lower := (rows 35 194 268 76 49 32 64 128 256), losses := [] }

theorem u38928 : Upper (D 6) (R 6) [34,192,264,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38929 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 268 76 50 53 85 149 277), lower := (rows 35 194 268 76 50 32 64 128 256), losses := [] }

theorem u38929 : Upper (D 6) (R 6) [34,192,264,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38930 : Route 9 := (fun mask => (mask,id))

def c38930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38930 : Upper (D 6) (R 6) [34,192,264,68,36] 13 := by
  apply FastRouting.sound _ _ [34,192,264,68,36] 13 (by decide) (choices 1) [1,2,16] r38930 c38930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25072
  · exact u25073
  · exact u25074

def b38931 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 268 88 19 37 101 165 293), lower := (rows 35 194 268 88 19 32 64 128 256), losses := [] }

theorem u38931 : Upper (D 6) (R 6) [34,192,264,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38932 : Route 9 := (fun mask => (mask,id))

def c38932 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38932 : Upper (D 6) (R 6) [34,192,264,80,5] 13 := by
  apply FastRouting.sound _ _ [34,192,264,80,5] 13 (by decide) (choices 1) [1,2,4] r38932 c38932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25075
  · exact u25076
  · exact u25077

def r38933 : Route 9 := (fun mask => (mask,id))

def c38933 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38933 : Upper (D 6) (R 6) [34,192,264,80,6] 13 := by
  apply FastRouting.sound _ _ [34,192,264,80,6] 13 (by decide) (choices 1) [1,4] r38933 c38933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25078
  · exact u25079

def b38934 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 268 88 49 39 71 135 263), lower := (rows 35 194 268 88 49 32 64 128 256), losses := [] }

theorem u38934 : Upper (D 6) (R 6) [34,192,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38935 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 268 88 50 37 69 133 261), lower := (rows 35 194 268 88 50 32 64 128 256), losses := [] }

theorem u38935 : Upper (D 6) (R 6) [34,192,264,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38936 : Route 9 := (fun mask => (mask,id))

def c38936 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38936 : Upper (D 6) (R 6) [34,192,264,80,36] 13 := by
  apply FastRouting.sound _ _ [34,192,264,80,36] 13 (by decide) (choices 1) [1,2,4] r38936 c38936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25080
  · exact u25081
  · exact u25082

def b38937 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 194 268 104 19 53 85 149 277), lower := (rows 35 194 268 104 19 32 64 128 256), losses := [] }

theorem u38937 : Upper (D 6) (R 6) [34,192,264,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38938 : Route 9 := (fun mask => (mask,id))

def c38938 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38938 : Upper (D 6) (R 6) [34,192,264,96,5] 13 := by
  apply FastRouting.sound _ _ [34,192,264,96,5] 13 (by decide) (choices 1) [1,2,4,16] r38938 c38938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25083
  · exact u25084
  · exact u25085
  · exact u25086

def r38939 : Route 9 := (fun mask => (mask,id))

def c38939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38939 : Upper (D 6) (R 6) [34,192,264,96,6] 13 := by
  apply FastRouting.sound _ _ [34,192,264,96,6] 13 (by decide) (choices 1) [1,4,16] r38939 c38939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25087
  · exact u25088
  · exact u25089

#print axioms u38939
end Delivery.IrregularNine14.P06
