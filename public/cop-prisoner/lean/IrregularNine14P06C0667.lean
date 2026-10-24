import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0446
import IrregularNine14P06C0447
import IrregularNine14P06C0448

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40020 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 292 11 21 114 82 210 338), lower := (rows 41 134 292 11 21 32 64 128 256), losses := [] }

theorem u40020 : Upper (D 6) (R 6) [40,132,288,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40021 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 292 11 22 113 81 209 337), lower := (rows 41 134 292 11 22 32 64 128 256), losses := [] }

theorem u40021 : Upper (D 6) (R 6) [40,132,288,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40022 : Route 9 := (fun mask => (mask,id))

def c40022 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40022 : Upper (D 6) (R 6) [40,132,288,3,65] 13 := by
  apply FastRouting.sound _ _ [40,132,288,3,65] 13 (by decide) (choices 1) [2,4,16,64] r40022 c40022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26781
  · exact u26782
  · exact u26783
  · exact u26784

def r40023 : Route 9 := (fun mask => (mask,id))

def c40023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40023 : Upper (D 6) (R 6) [40,132,288,3,66] 13 := by
  apply FastRouting.sound _ _ [40,132,288,3,66] 13 (by decide) (choices 1) [1,4,16,64] r40023 c40023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26785
  · exact u26786
  · exact u26787
  · exact u26788

def r40024 : Route 9 := (fun mask => (mask,id))

def c40024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40024 : Upper (D 6) (R 6) [40,132,288,3,68] 13 := by
  apply FastRouting.sound _ _ [40,132,288,3,68] 13 (by decide) (choices 1) [1,2,16,64] r40024 c40024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26789
  · exact u26790
  · exact u26791
  · exact u26792

def b40025 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 134 292 25 19 102 70 198 326), lower := (rows 41 134 292 25 19 32 64 128 256), losses := [] }

theorem u40025 : Upper (D 6) (R 6) [40,132,288,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40026 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 25, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 134 292 25 21 98 66 194 322), lower := (rows 41 134 292 25 21 32 64 128 256), losses := [] }

theorem u40026 : Upper (D 6) (R 6) [40,132,288,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40027 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 292 25 22 99 67 195 323), lower := (rows 41 134 292 25 22 32 64 128 256), losses := [] }

theorem u40027 : Upper (D 6) (R 6) [40,132,288,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40028 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 134 292 25 81 102 70 198 326), lower := (rows 41 134 292 25 81 32 64 128 256), losses := [] }

theorem u40028 : Upper (D 6) (R 6) [40,132,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40029 : Route 9 := (fun mask => (mask,id))

def c40029 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40029 : Upper (D 6) (R 6) [40,132,288,17,66] 13 := by
  apply FastRouting.sound _ _ [40,132,288,17,66] 13 (by decide) (choices 1) [1,2,4,64] r40029 c40029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26793
  · exact u26794
  · exact u26795
  · exact u26796

def r40030 : Route 9 := (fun mask => (mask,id))

def c40030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40030 : Upper (D 6) (R 6) [40,132,288,17,68] 13 := by
  apply FastRouting.sound _ _ [40,132,288,17,68] 13 (by decide) (choices 1) [1,2,64] r40030 c40030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26797
  · exact u26798
  · exact u26799

def b40031 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 134 292 26 19 101 69 197 325), lower := (rows 41 134 292 26 19 32 64 128 256), losses := [] }

theorem u40031 : Upper (D 6) (R 6) [40,132,288,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40032 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 32 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(3,5)], upper := (rows 41 134 292 26 21 99 67 195 323), lower := (rows 41 134 292 26 21 32 64 128 256), losses := [] }

theorem u40032 : Upper (D 6) (R 6) [40,132,288,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40033 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 134 292 26 22 97 65 193 321), lower := (rows 41 134 292 26 22 32 64 128 256), losses := [] }

theorem u40033 : Upper (D 6) (R 6) [40,132,288,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40034 : Route 9 := (fun mask => (mask,id))

def c40034 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40034 : Upper (D 6) (R 6) [40,132,288,18,65] 13 := by
  apply FastRouting.sound _ _ [40,132,288,18,65] 13 (by decide) (choices 1) [1,2,4,64] r40034 c40034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26800
  · exact u26801
  · exact u26802
  · exact u26803

def b40035 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 134 292 26 82 101 69 197 325), lower := (rows 41 134 292 26 82 32 64 128 256), losses := [] }

theorem u40035 : Upper (D 6) (R 6) [40,132,288,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40036 : Route 9 := (fun mask => (mask,id))

def c40036 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40036 : Upper (D 6) (R 6) [40,132,288,18,68] 13 := by
  apply FastRouting.sound _ _ [40,132,288,18,68] 13 (by decide) (choices 1) [1,2,64] r40036 c40036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26804
  · exact u26805
  · exact u26806

def b40037 : PairBound 9 := { available := 67, camps := [], pairs := [(0,2),(1,5),(4,5)], upper := (rows 41 134 292 28 19 99 67 195 323), lower := (rows 41 134 292 28 19 32 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 48 80 144 272), good := (rows 41 130 288 505 499 32 64 128 256) },{ target := 5, region := (rows 1 10 4 8 17 0 81 145 273), good := (rows 475 134 260 478 467 0 64 128 256) }] }

theorem u40037 : Upper (D 6) (R 6) [40,132,288,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40038 : Route 9 := (fun mask => (mask,id))

def c40038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40038 : Upper (D 6) (R 6) [40,132,288,20,65] 13 := by
  apply FastRouting.sound _ _ [40,132,288,20,65] 13 (by decide) (choices 1) [1,2,64] r40038 c40038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26807
  · exact u26808
  · exact u26809

def r40039 : Route 9 := (fun mask => (mask,id))

def c40039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40039 : Upper (D 6) (R 6) [40,132,288,20,66] 13 := by
  apply FastRouting.sound _ _ [40,132,288,20,66] 13 (by decide) (choices 1) [1,2,64] r40039 c40039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26810
  · exact u26811
  · exact u26812

def r40040 : Route 9 := (fun mask => (mask,id))

def c40040 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40040 : Upper (D 6) (R 6) [40,132,288,65,3] 13 := by
  apply FastRouting.sound _ _ [40,132,288,65,3] 13 (by decide) (choices 1) [2,4,16,64] r40040 c40040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26813
  · exact u26814
  · exact u26815
  · exact u26816

def b40041 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 134 292 73 21 114 82 210 338), lower := (rows 41 134 292 73 21 32 64 128 256), losses := [] }

theorem u40041 : Upper (D 6) (R 6) [40,132,288,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40042 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 292 73 22 115 83 211 339), lower := (rows 41 134 292 73 22 32 64 128 256), losses := [] }

theorem u40042 : Upper (D 6) (R 6) [40,132,288,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40043 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 134 292 73 81 54 86 150 278), lower := (rows 41 134 292 73 81 32 64 128 256), losses := [] }

theorem u40043 : Upper (D 6) (R 6) [40,132,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40044 : Route 9 := (fun mask => (mask,id))

def c40044 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40044 : Upper (D 6) (R 6) [40,132,288,65,66] 13 := by
  apply FastRouting.sound _ _ [40,132,288,65,66] 13 (by decide) (choices 1) [1,2,4,16] r40044 c40044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26817
  · exact u26818
  · exact u26819
  · exact u26820

def r40045 : Route 9 := (fun mask => (mask,id))

def c40045 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40045 : Upper (D 6) (R 6) [40,132,288,65,68] 13 := by
  apply FastRouting.sound _ _ [40,132,288,65,68] 13 (by decide) (choices 1) [1,2,16] r40045 c40045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26821
  · exact u26822
  · exact u26823

def r40046 : Route 9 := (fun mask => (mask,id))

def c40046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40046 : Upper (D 6) (R 6) [40,132,288,66,3] 13 := by
  apply FastRouting.sound _ _ [40,132,288,66,3] 13 (by decide) (choices 1) [1,4,16,64] r40046 c40046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26824
  · exact u26825
  · exact u26826
  · exact u26827

def r40047 : Route 9 := (fun mask => (mask,id))

def c40047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40047 : Upper (D 6) (R 6) [40,132,288,66,5] 13 := by
  apply FastRouting.sound _ _ [40,132,288,66,5] 13 (by decide) (choices 1) [1,2,16,64] r40047 c40047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26828
  · exact u26829
  · exact u26830
  · exact u26831

def b40048 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 292 74 22 113 81 209 337), lower := (rows 41 134 292 74 22 32 64 128 256), losses := [] }

theorem u40048 : Upper (D 6) (R 6) [40,132,288,66,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40049 : Route 9 := (fun mask => (mask,id))

def c40049 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40049 : Upper (D 6) (R 6) [40,132,288,66,65] 13 := by
  apply FastRouting.sound _ _ [40,132,288,66,65] 13 (by decide) (choices 1) [1,2,4,16] r40049 c40049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26832
  · exact u26833
  · exact u26834
  · exact u26835

def b40050 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 134 292 74 82 53 85 149 277), lower := (rows 41 134 292 74 82 32 64 128 256), losses := [] }

theorem u40050 : Upper (D 6) (R 6) [40,132,288,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40051 : Route 9 := (fun mask => (mask,id))

def c40051 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40051 : Upper (D 6) (R 6) [40,132,288,66,68] 13 := by
  apply FastRouting.sound _ _ [40,132,288,66,68] 13 (by decide) (choices 1) [1,2,16] r40051 c40051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26836
  · exact u26837
  · exact u26838

def r40052 : Route 9 := (fun mask => (mask,id))

def c40052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40052 : Upper (D 6) (R 6) [40,132,288,68,3] 13 := by
  apply FastRouting.sound _ _ [40,132,288,68,3] 13 (by decide) (choices 1) [1,2,16,64] r40052 c40052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26839
  · exact u26840
  · exact u26841
  · exact u26842

def r40053 : Route 9 := (fun mask => (mask,id))

def c40053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40053 : Upper (D 6) (R 6) [40,132,288,68,65] 13 := by
  apply FastRouting.sound _ _ [40,132,288,68,65] 13 (by decide) (choices 1) [1,2,16] r40053 c40053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26843
  · exact u26844
  · exact u26845

def r40054 : Route 9 := (fun mask => (mask,id))

def c40054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40054 : Upper (D 6) (R 6) [40,132,288,68,66] 13 := by
  apply FastRouting.sound _ _ [40,132,288,68,66] 13 (by decide) (choices 1) [1,2,16] r40054 c40054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26846
  · exact u26847
  · exact u26848

def r40055 : Route 9 := (fun mask => (mask,id))

def c40055 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40055 : Upper (D 6) (R 6) [40,132,288,80,3] 13 := by
  apply FastRouting.sound _ _ [40,132,288,80,3] 13 (by decide) (choices 1) [1,2,4,64] r40055 c40055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26849
  · exact u26850
  · exact u26851
  · exact u26852

def r40056 : Route 9 := (fun mask => (mask,id))

def c40056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40056 : Upper (D 6) (R 6) [40,132,288,80,5] 13 := by
  apply FastRouting.sound _ _ [40,132,288,80,5] 13 (by decide) (choices 1) [1,2,64] r40056 c40056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26853
  · exact u26854
  · exact u26855

def b40057 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 292 88 22 99 67 195 323), lower := (rows 41 134 292 88 22 32 64 128 256), losses := [] }

theorem u40057 : Upper (D 6) (R 6) [40,132,288,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40058 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 134 292 88 81 39 71 135 263), lower := (rows 41 134 292 88 81 32 64 128 256), losses := [] }

theorem u40058 : Upper (D 6) (R 6) [40,132,288,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40059 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 134 292 88 82 39 71 135 263), lower := (rows 41 134 292 88 82 32 64 128 256), losses := [] }

theorem u40059 : Upper (D 6) (R 6) [40,132,288,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40060 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 41 134 292 88 84 35 67 131 259), lower := (rows 41 134 292 88 84 32 64 128 256), losses := [] }

theorem u40060 : Upper (D 6) (R 6) [40,132,288,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40061 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 41 134 324 11 19 116 116 244 372), lower := (rows 41 134 324 11 19 32 64 128 256), losses := [] }

theorem u40061 : Upper (D 6) (R 6) [40,132,320,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40062 : Route 9 := (fun mask => (mask,id))

def c40062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40062 : Upper (D 6) (R 6) [40,132,320,3,5] 13 := by
  apply FastRouting.sound _ _ [40,132,320,3,5] 13 (by decide) (choices 1) [2,16,64] r40062 c40062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26856
  · exact u26857
  · exact u26858

def b40063 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 324 11 22 113 113 241 369), lower := (rows 41 134 324 11 22 32 64 128 256), losses := [] }

theorem u40063 : Upper (D 6) (R 6) [40,132,320,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40064 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 324 11 49 118 86 214 342), lower := (rows 41 134 324 11 49 32 64 128 256), losses := [] }

theorem u40064 : Upper (D 6) (R 6) [40,132,320,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40065 : PairBound 9 := { available := 85, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 324 11 50 117 85 213 341), lower := (rows 41 134 324 11 50 32 64 128 256), losses := [] }

theorem u40065 : Upper (D 6) (R 6) [40,132,320,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40066 : Route 9 := (fun mask => (mask,id))

def c40066 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40066 : Upper (D 6) (R 6) [40,132,320,3,36] 13 := by
  apply FastRouting.sound _ _ [40,132,320,3,36] 13 (by decide) (choices 1) [1,2,16,64] r40066 c40066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26859
  · exact u26860
  · exact u26861
  · exact u26862

def r40067 : Route 9 := (fun mask => (mask,id))

def c40067 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40067 : Upper (D 6) (R 6) [40,132,320,3,65] 13 := by
  apply FastRouting.sound _ _ [40,132,320,3,65] 13 (by decide) (choices 1) [2,4,16] r40067 c40067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26863
  · exact u26864
  · exact u26865

def r40068 : Route 9 := (fun mask => (mask,id))

def c40068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40068 : Upper (D 6) (R 6) [40,132,320,3,66] 13 := by
  apply FastRouting.sound _ _ [40,132,320,3,66] 13 (by decide) (choices 1) [1,4,16] r40068 c40068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26866
  · exact u26867
  · exact u26868

def b40069 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 134 324 11 84 51 115 179 307), lower := (rows 41 134 324 11 84 32 64 128 256), losses := [] }

theorem u40069 : Upper (D 6) (R 6) [40,132,320,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40070 : Route 9 := (fun mask => (mask,id))

def c40070 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40070 : Upper (D 6) (R 6) [40,132,320,3,96] 13 := by
  apply FastRouting.sound _ _ [40,132,320,3,96] 13 (by decide) (choices 1) [1,2,4,16] r40070 c40070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26869
  · exact u26870
  · exact u26871
  · exact u26872

def r40071 : Route 9 := (fun mask => (mask,id))

def c40071 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40071 : Upper (D 6) (R 6) [40,132,320,5,3] 13 := by
  apply FastRouting.sound _ _ [40,132,320,5,3] 13 (by decide) (choices 1) [2,16,64] r40071 c40071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26873
  · exact u26874
  · exact u26875

def b40072 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 134 324 13 49 114 82 210 338), lower := (rows 41 134 324 13 49 32 64 128 256), losses := [] }

theorem u40072 : Upper (D 6) (R 6) [40,132,320,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40073 : Route 9 := (fun mask => (mask,id))

def c40073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40073 : Upper (D 6) (R 6) [40,132,320,5,34] 13 := by
  apply FastRouting.sound _ _ [40,132,320,5,34] 13 (by decide) (choices 1) [1,2,16,64] r40073 c40073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26876
  · exact u26877
  · exact u26878
  · exact u26879

def r40074 : Route 9 := (fun mask => (mask,id))

def c40074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40074 : Upper (D 6) (R 6) [40,132,320,5,65] 13 := by
  apply FastRouting.sound _ _ [40,132,320,5,65] 13 (by decide) (choices 1) [2,16] r40074 c40074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26880
  · exact u26881

def r40075 : Route 9 := (fun mask => (mask,id))

def c40075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40075 : Upper (D 6) (R 6) [40,132,320,5,66] 13 := by
  apply FastRouting.sound _ _ [40,132,320,5,66] 13 (by decide) (choices 1) [1,2,16] r40075 c40075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26882
  · exact u26883
  · exact u26884

def r40076 : Route 9 := (fun mask => (mask,id))

def c40076 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40076 : Upper (D 6) (R 6) [40,132,320,5,96] 13 := by
  apply FastRouting.sound _ _ [40,132,320,5,96] 13 (by decide) (choices 1) [1,2,16] r40076 c40076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26885
  · exact u26886
  · exact u26887

def b40077 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 134 324 25 19 102 102 230 358), lower := (rows 41 134 324 25 19 32 64 128 256), losses := [] }

theorem u40077 : Upper (D 6) (R 6) [40,132,320,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40078 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 134 324 25 21 98 98 226 354), lower := (rows 41 134 324 25 21 32 64 128 256), losses := [] }

theorem u40078 : Upper (D 6) (R 6) [40,132,320,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40079 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 134 324 25 22 99 99 227 355), lower := (rows 41 134 324 25 22 32 64 128 256), losses := [] }

theorem u40079 : Upper (D 6) (R 6) [40,132,320,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40079
end Delivery.IrregularNine14.P06
