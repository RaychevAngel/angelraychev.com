import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0381
import IrregularNine14P07C0382
import IrregularNine14P07C0383

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36960 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 20, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 37 74 22 392 82 161 225 161 417), lower := (rows 37 74 22 392 82 32 64 128 256), losses := [] }

theorem u36960 : Upper (D 7) (R 7) [36,72,18,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36961 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(1,5),(3,5),(3,6)], upper := (rows 37 74 22 392 112 163 195 131 387), lower := (rows 37 74 22 392 112 32 64 128 256), losses := [] }

theorem u36961 : Upper (D 7) (R 7) [36,72,18,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36962 : Route 9 := (fun mask => (mask,id))

def c36962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36962 : Upper (D 7) (R 7) [36,72,18,384,129] 13 := by
  apply FastRouting.sound _ _ [36,72,18,384,129] 13 (by decide) (choices 1) [1,2,64] r36962 c36962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22889
  · exact u22890
  · exact u22891

def b36963 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 4, targets := 97 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,6)], upper := (rows 37 74 22 392 146 97 97 225 353), lower := (rows 37 74 22 392 146 32 64 128 256), losses := [] }

theorem u36963 : Upper (D 7) (R 7) [36,72,18,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36964 : Route 9 := (fun mask => (mask,id))

def c36964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36964 : Upper (D 7) (R 7) [36,72,18,384,160] 13 := by
  apply FastRouting.sound _ _ [36,72,18,384,160] 13 (by decide) (choices 1) [1,2,64] r36964 c36964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22892
  · exact u22893
  · exact u22894

def r36965 : Route 9 := (fun mask => (mask,id))

def c36965 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36965 : Upper (D 7) (R 7) [36,72,18,384,192] 13 := by
  apply FastRouting.sound _ _ [36,72,18,384,192] 13 (by decide) (choices 1) [1,2] r36965 c36965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22895
  · exact u22896

def b36966 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 3, region := 450, targets := 32 },{ cop := 4, region := 452, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(3,0)], upper := (rows 37 74 69 56 19 418 450 386 386), lower := (rows 37 74 69 56 19 32 64 128 256), losses := [] }

theorem u36966 : Upper (D 7) (R 7) [36,72,65,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36967 : Route 9 := (fun mask => (mask,id))

def c36967 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36967 : Upper (D 7) (R 7) [36,72,65,48,129] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48,129] 13 (by decide) (choices 1) [2,128,256] r36967 c36967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22897
  · exact u22898
  · exact u22899

def r36968 : Route 9 := (fun mask => (mask,id))

def c36968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36968 : Upper (D 7) (R 7) [36,72,65,48,130] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48,130] 13 (by decide) (choices 1) [1,2,128,256] r36968 c36968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22900
  · exact u22901
  · exact u22902
  · exact u22903

def r36969 : Route 9 := (fun mask => (mask,id))

def c36969 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36969 : Upper (D 7) (R 7) [36,72,65,48,257] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48,257] 13 (by decide) (choices 1) [2,128] r36969 c36969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22904
  · exact u22905

def r36970 : Route 9 := (fun mask => (mask,id))

def c36970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36970 : Upper (D 7) (R 7) [36,72,65,48,258] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48,258] 13 (by decide) (choices 1) [1,2,128] r36970 c36970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22906
  · exact u22907
  · exact u22908

def r36971 : Route 9 := (fun mask => (mask,id))

def c36971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36971 : Upper (D 7) (R 7) [36,72,65,48,384] 13 := by
  apply FastRouting.sound _ _ [36,72,65,48,384] 13 (by decide) (choices 1) [1,2,128] r36971 c36971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22909
  · exact u22910
  · exact u22911

def r36972 : Route 9 := (fun mask => (mask,id))

def c36972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u36972 : Upper (D 7) (R 7) [36,72,65,129,34] 13 := by
  apply FastRouting.sound _ _ [36,72,65,129,34] 13 (by decide) (choices 1) [2,16,128,256] r36972 c36972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22912
  · exact u22913
  · exact u22914
  · exact u22915

def b36973 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 69 137 146 306 370 434 306), lower := (rows 37 74 69 137 146 32 64 128 256), losses := [] }

theorem u36973 : Upper (D 7) (R 7) [36,72,65,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36974 : Route 9 := (fun mask => (mask,id))

def c36974 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36974 : Upper (D 7) (R 7) [36,72,65,129,160] 13 := by
  apply FastRouting.sound _ _ [36,72,65,129,160] 13 (by decide) (choices 1) [2,16,256] r36974 c36974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22916
  · exact u22917
  · exact u22918

def r36975 : Route 9 := (fun mask => (mask,id))

def c36975 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36975 : Upper (D 7) (R 7) [36,72,65,129,258] 13 := by
  apply FastRouting.sound _ _ [36,72,65,129,258] 13 (by decide) (choices 1) [2,16,128] r36975 c36975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22919
  · exact u22920
  · exact u22921

def r36976 : Route 9 := (fun mask => (mask,id))

def c36976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36976 : Upper (D 7) (R 7) [36,72,65,129,288] 13 := by
  apply FastRouting.sound _ _ [36,72,65,129,288] 13 (by decide) (choices 1) [2,16,128] r36976 c36976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22922
  · exact u22923
  · exact u22924

def r36977 : Route 9 := (fun mask => (mask,id))

def c36977 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36977 : Upper (D 7) (R 7) [36,72,65,129,384] 13 := by
  apply FastRouting.sound _ _ [36,72,65,129,384] 13 (by decide) (choices 1) [2,16] r36977 c36977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22925
  · exact u22926

def b36978 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 69 138 19 432 496 432 432), lower := (rows 37 74 69 138 19 32 64 128 256), losses := [] }

theorem u36978 : Upper (D 7) (R 7) [36,72,65,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36979 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 69 138 49 434 466 402 402), lower := (rows 37 74 69 138 49 32 64 128 256), losses := [] }

theorem u36979 : Upper (D 7) (R 7) [36,72,65,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36980 : Route 9 := (fun mask => (mask,id))

def c36980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u36980 : Upper (D 7) (R 7) [36,72,65,130,34] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,34] 13 (by decide) (choices 1) [1,16,128,256] r36980 c36980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22927
  · exact u22928
  · exact u22929
  · exact u22930

def r36981 : Route 9 := (fun mask => (mask,id))

def c36981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36981 : Upper (D 7) (R 7) [36,72,65,130,129] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,129] 13 (by decide) (choices 1) [2,16,256] r36981 c36981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22931
  · exact u22932
  · exact u22933

def b36982 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 74 69 138 146 305 369 433 305), lower := (rows 37 74 69 138 146 32 64 128 256), losses := [] }

theorem u36982 : Upper (D 7) (R 7) [36,72,65,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36983 : Route 9 := (fun mask => (mask,id))

def c36983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36983 : Upper (D 7) (R 7) [36,72,65,130,160] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,160] 13 (by decide) (choices 1) [1,2,16,256] r36983 c36983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22934
  · exact u22935
  · exact u22936
  · exact u22937

def r36984 : Route 9 := (fun mask => (mask,id))

def c36984 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36984 : Upper (D 7) (R 7) [36,72,65,130,257] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,257] 13 (by decide) (choices 1) [2,16,128] r36984 c36984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22938
  · exact u22939
  · exact u22940

def r36985 : Route 9 := (fun mask => (mask,id))

def c36985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36985 : Upper (D 7) (R 7) [36,72,65,130,258] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,258] 13 (by decide) (choices 1) [1,16,128] r36985 c36985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22941
  · exact u22942
  · exact u22943

def r36986 : Route 9 := (fun mask => (mask,id))

def c36986 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36986 : Upper (D 7) (R 7) [36,72,65,130,288] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,288] 13 (by decide) (choices 1) [1,2,16,128] r36986 c36986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22944
  · exact u22945
  · exact u22946
  · exact u22947

def r36987 : Route 9 := (fun mask => (mask,id))

def c36987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36987 : Upper (D 7) (R 7) [36,72,65,130,384] 13 := by
  apply FastRouting.sound _ _ [36,72,65,130,384] 13 (by decide) (choices 1) [1,2,16] r36987 c36987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22948
  · exact u22949
  · exact u22950

def r36988 : Route 9 := (fun mask => (mask,id))

def c36988 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36988 : Upper (D 7) (R 7) [36,72,65,144,3] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144,3] 13 (by decide) (choices 1) [2,128,256] r36988 c36988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22951
  · exact u22952
  · exact u22953

def b36989 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 69 152 49 418 450 386 386), lower := (rows 37 74 69 152 49 32 64 128 256), losses := [] }

theorem u36989 : Upper (D 7) (R 7) [36,72,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36990 : Route 9 := (fun mask => (mask,id))

def c36990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u36990 : Upper (D 7) (R 7) [36,72,65,144,34] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144,34] 13 (by decide) (choices 1) [1,2,128,256] r36990 c36990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22954
  · exact u22955
  · exact u22956
  · exact u22957

def b36991 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 37 74 69 152 145 290 354 418 290), lower := (rows 37 74 69 152 145 32 64 128 256), losses := [] }

theorem u36991 : Upper (D 7) (R 7) [36,72,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36992 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 74 69 152 146 291 355 419 291), lower := (rows 37 74 69 152 146 32 64 128 256), losses := [] }

theorem u36992 : Upper (D 7) (R 7) [36,72,65,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36993 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 74 69 152 176 291 323 387 259), lower := (rows 37 74 69 152 176 32 64 128 256), losses := [] }

theorem u36993 : Upper (D 7) (R 7) [36,72,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36994 : Route 9 := (fun mask => (mask,id))

def c36994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36994 : Upper (D 7) (R 7) [36,72,65,144,257] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144,257] 13 (by decide) (choices 1) [2,128] r36994 c36994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22958
  · exact u22959

def r36995 : Route 9 := (fun mask => (mask,id))

def c36995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36995 : Upper (D 7) (R 7) [36,72,65,144,258] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144,258] 13 (by decide) (choices 1) [1,2,128] r36995 c36995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22960
  · exact u22961
  · exact u22962

def r36996 : Route 9 := (fun mask => (mask,id))

def c36996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36996 : Upper (D 7) (R 7) [36,72,65,144,288] 13 := by
  apply FastRouting.sound _ _ [36,72,65,144,288] 13 (by decide) (choices 1) [1,2,128] r36996 c36996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22963
  · exact u22964
  · exact u22965

def b36997 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 74 69 152 400 35 99 163 291), lower := (rows 37 74 69 152 400 32 64 128 256), losses := [] }

theorem u36997 : Upper (D 7) (R 7) [36,72,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36998 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 452, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,0),(2,5),(3,0),(3,6)], upper := (rows 37 74 69 168 19 434 466 402 402), lower := (rows 37 74 69 168 19 32 64 128 256), losses := [] }

theorem u36998 : Upper (D 7) (R 7) [36,72,65,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36999 : Route 9 := (fun mask => (mask,id))

def c36999 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36999 : Upper (D 7) (R 7) [36,72,65,160,129] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,129] 13 (by decide) (choices 1) [2,16,256] r36999 c36999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22966
  · exact u22967
  · exact u22968

def r37000 : Route 9 := (fun mask => (mask,id))

def c37000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37000 : Upper (D 7) (R 7) [36,72,65,160,130] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,130] 13 (by decide) (choices 1) [1,2,16,256] r37000 c37000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22969
  · exact u22970
  · exact u22971
  · exact u22972

def r37001 : Route 9 := (fun mask => (mask,id))

def c37001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37001 : Upper (D 7) (R 7) [36,72,65,160,257] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,257] 13 (by decide) (choices 1) [2,16,128] r37001 c37001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22973
  · exact u22974
  · exact u22975

def r37002 : Route 9 := (fun mask => (mask,id))

def c37002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37002 : Upper (D 7) (R 7) [36,72,65,160,258] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,258] 13 (by decide) (choices 1) [1,2,16,128] r37002 c37002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22976
  · exact u22977
  · exact u22978
  · exact u22979

def r37003 : Route 9 := (fun mask => (mask,id))

def c37003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37003 : Upper (D 7) (R 7) [36,72,65,160,384] 13 := by
  apply FastRouting.sound _ _ [36,72,65,160,384] 13 (by decide) (choices 1) [1,2,16] r37003 c37003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22980
  · exact u22981
  · exact u22982

def r37004 : Route 9 := (fun mask => (mask,id))

def c37004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37004 : Upper (D 7) (R 7) [36,72,65,257,34] 13 := by
  apply FastRouting.sound _ _ [36,72,65,257,34] 13 (by decide) (choices 1) [2,16,128] r37004 c37004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22983
  · exact u22984
  · exact u22985

def r37005 : Route 9 := (fun mask => (mask,id))

def c37005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37005 : Upper (D 7) (R 7) [36,72,65,257,130] 13 := by
  apply FastRouting.sound _ _ [36,72,65,257,130] 13 (by decide) (choices 1) [2,16,128] r37005 c37005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22986
  · exact u22987
  · exact u22988

def r37006 : Route 9 := (fun mask => (mask,id))

def c37006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37006 : Upper (D 7) (R 7) [36,72,65,257,160] 13 := by
  apply FastRouting.sound _ _ [36,72,65,257,160] 13 (by decide) (choices 1) [2,16,128] r37006 c37006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22989
  · exact u22990
  · exact u22991

def b37007 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 69 266 19 176 240 176 432), lower := (rows 37 74 69 266 19 32 64 128 256), losses := [] }

theorem u37007 : Upper (D 7) (R 7) [36,72,65,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37008 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 69 266 49 178 210 146 402), lower := (rows 37 74 69 266 49 32 64 128 256), losses := [] }

theorem u37008 : Upper (D 7) (R 7) [36,72,65,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37009 : Route 9 := (fun mask => (mask,id))

def c37009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37009 : Upper (D 7) (R 7) [36,72,65,258,34] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258,34] 13 (by decide) (choices 1) [1,16,128] r37009 c37009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22992
  · exact u22993
  · exact u22994

def r37010 : Route 9 := (fun mask => (mask,id))

def c37010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37010 : Upper (D 7) (R 7) [36,72,65,258,129] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258,129] 13 (by decide) (choices 1) [2,16,128] r37010 c37010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22995
  · exact u22996
  · exact u22997

def r37011 : Route 9 := (fun mask => (mask,id))

def c37011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37011 : Upper (D 7) (R 7) [36,72,65,258,130] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258,130] 13 (by decide) (choices 1) [1,16,128] r37011 c37011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22998
  · exact u22999
  · exact u23000

def r37012 : Route 9 := (fun mask => (mask,id))

def c37012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37012 : Upper (D 7) (R 7) [36,72,65,258,160] 13 := by
  apply FastRouting.sound _ _ [36,72,65,258,160] 13 (by decide) (choices 1) [1,2,16,128] r37012 c37012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23001
  · exact u23002
  · exact u23003
  · exact u23004

def r37013 : Route 9 := (fun mask => (mask,id))

def c37013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37013 : Upper (D 7) (R 7) [36,72,65,272,3] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,3] 13 (by decide) (choices 1) [2,128] r37013 c37013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23005
  · exact u23006

def b37014 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 69 280 49 162 194 130 386), lower := (rows 37 74 69 280 49 32 64 128 256), losses := [] }

theorem u37014 : Upper (D 7) (R 7) [36,72,65,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37015 : Route 9 := (fun mask => (mask,id))

def c37015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37015 : Upper (D 7) (R 7) [36,72,65,272,34] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,34] 13 (by decide) (choices 1) [1,2,128] r37015 c37015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23007
  · exact u23008
  · exact u23009

def r37016 : Route 9 := (fun mask => (mask,id))

def c37016 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37016 : Upper (D 7) (R 7) [36,72,65,272,129] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,129] 13 (by decide) (choices 1) [2,128] r37016 c37016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23010
  · exact u23011

def r37017 : Route 9 := (fun mask => (mask,id))

def c37017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37017 : Upper (D 7) (R 7) [36,72,65,272,130] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,130] 13 (by decide) (choices 1) [1,2,128] r37017 c37017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23012
  · exact u23013
  · exact u23014

def r37018 : Route 9 := (fun mask => (mask,id))

def c37018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37018 : Upper (D 7) (R 7) [36,72,65,272,160] 13 := by
  apply FastRouting.sound _ _ [36,72,65,272,160] 13 (by decide) (choices 1) [1,2,128] r37018 c37018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23015
  · exact u23016
  · exact u23017

def b37019 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 196, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,0),(2,5),(3,0),(3,6)], upper := (rows 37 74 69 296 19 178 210 146 402), lower := (rows 37 74 69 296 19 32 64 128 256), losses := [] }

theorem u37019 : Upper (D 7) (R 7) [36,72,65,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u37019
end Delivery.IrregularNine14.P07
