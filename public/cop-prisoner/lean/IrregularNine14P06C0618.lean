import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0365
import IrregularNine14P06C0366
import IrregularNine14P06C0367

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37080 : Route 9 := (fun mask => (mask,id))

def c37080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37080 : Upper (D 6) (R 6) [34,129,66,65,264] 13 := by
  apply FastRouting.sound _ _ [34,129,66,65,264] 13 (by decide) (choices 1) [4,16] r37080 c37080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21939
  · exact u21940

def r37081 : Route 9 := (fun mask => (mask,id))

def c37081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37081 : Upper (D 6) (R 6) [34,129,66,65,288] 13 := by
  apply FastRouting.sound _ _ [34,129,66,65,288] 13 (by decide) (choices 1) [4,8,16] r37081 c37081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21941
  · exact u21942
  · exact u21943

def b37082 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 76 273 60 124 188 316), lower := (rows 35 131 70 76 273 32 64 128 256), losses := [] }

theorem u37082 : Upper (D 6) (R 6) [34,129,66,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37083 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 76 276 57 121 185 313), lower := (rows 35 131 70 76 276 32 64 128 256), losses := [] }

theorem u37083 : Upper (D 6) (R 6) [34,129,66,68,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37084 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 76 280 53 117 181 309), lower := (rows 35 131 70 76 280 32 64 128 256), losses := [] }

theorem u37084 : Upper (D 6) (R 6) [34,129,66,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37085 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 70 76 304 61 93 157 285), lower := (rows 35 131 70 76 304 32 64 128 256), losses := [] }

theorem u37085 : Upper (D 6) (R 6) [34,129,66,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37086 : Route 9 := (fun mask => (mask,id))

def c37086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37086 : Upper (D 6) (R 6) [34,129,66,80,257] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80,257] 13 (by decide) (choices 1) [4,8] r37086 c37086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21944
  · exact u21945

def r37087 : Route 9 := (fun mask => (mask,id))

def c37087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37087 : Upper (D 6) (R 6) [34,129,66,80,260] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80,260] 13 (by decide) (choices 1) [1,4,8] r37087 c37087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21946
  · exact u21947
  · exact u21948

def r37088 : Route 9 := (fun mask => (mask,id))

def c37088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37088 : Upper (D 6) (R 6) [34,129,66,80,264] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80,264] 13 (by decide) (choices 1) [1,4] r37088 c37088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21949
  · exact u21950

def r37089 : Route 9 := (fun mask => (mask,id))

def c37089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37089 : Upper (D 6) (R 6) [34,129,66,80,288] 13 := by
  apply FastRouting.sound _ _ [34,129,66,80,288] 13 (by decide) (choices 1) [1,4,8] r37089 c37089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21951
  · exact u21952
  · exact u21953

def r37090 : Route 9 := (fun mask => (mask,id))

def c37090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37090 : Upper (D 6) (R 6) [34,129,66,96,257] 13 := by
  apply FastRouting.sound _ _ [34,129,66,96,257] 13 (by decide) (choices 1) [4,8,16] r37090 c37090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21954
  · exact u21955
  · exact u21956

def r37091 : Route 9 := (fun mask => (mask,id))

def c37091 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37091 : Upper (D 6) (R 6) [34,129,66,96,260] 13 := by
  apply FastRouting.sound _ _ [34,129,66,96,260] 13 (by decide) (choices 1) [1,4,8,16] r37091 c37091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21957
  · exact u21958
  · exact u21959
  · exact u21960

def r37092 : Route 9 := (fun mask => (mask,id))

def c37092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37092 : Upper (D 6) (R 6) [34,129,66,96,264] 13 := by
  apply FastRouting.sound _ _ [34,129,66,96,264] 13 (by decide) (choices 1) [1,4,16] r37092 c37092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21961
  · exact u21962
  · exact u21963

def r37093 : Route 9 := (fun mask => (mask,id))

def c37093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37093 : Upper (D 6) (R 6) [34,129,72,5,6] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,6] 13 (by decide) (choices 1) [16,64,256] r37093 c37093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21964
  · exact u21965
  · exact u21966

def b37094 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 76 13 50 372 340 468 340), lower := (rows 35 131 76 13 50 32 64 128 256), losses := [] }

theorem u37094 : Upper (D 6) (R 6) [34,129,72,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37095 : Route 9 := (fun mask => (mask,id))

def c37095 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37095 : Upper (D 6) (R 6) [34,129,72,5,36] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,36] 13 (by decide) (choices 1) [2,16,64,256] r37095 c37095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21967
  · exact u21968
  · exact u21969
  · exact u21970

def r37096 : Route 9 := (fun mask => (mask,id))

def c37096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37096 : Upper (D 6) (R 6) [34,129,72,5,66] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,66] 13 (by decide) (choices 1) [4,16,256] r37096 c37096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21971
  · exact u21972
  · exact u21973

def b37097 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 13 84 306 370 434 306), lower := (rows 35 131 76 13 84 32 64 128 256), losses := [] }

theorem u37097 : Upper (D 6) (R 6) [34,129,72,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37098 : Route 9 := (fun mask => (mask,id))

def c37098 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37098 : Upper (D 6) (R 6) [34,129,72,5,96] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,96] 13 (by decide) (choices 1) [2,4,16,256] r37098 c37098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21974
  · exact u21975
  · exact u21976
  · exact u21977

def r37099 : Route 9 := (fun mask => (mask,id))

def c37099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37099 : Upper (D 6) (R 6) [34,129,72,5,258] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,258] 13 (by decide) (choices 1) [4,16,64] r37099 c37099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21978
  · exact u21979
  · exact u21980

def r37100 : Route 9 := (fun mask => (mask,id))

def c37100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37100 : Upper (D 6) (R 6) [34,129,72,5,260] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,260] 13 (by decide) (choices 1) [2,16,64] r37100 c37100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21981
  · exact u21982
  · exact u21983

def r37101 : Route 9 := (fun mask => (mask,id))

def c37101 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37101 : Upper (D 6) (R 6) [34,129,72,5,288] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,288] 13 (by decide) (choices 1) [2,4,16,64] r37101 c37101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21984
  · exact u21985
  · exact u21986
  · exact u21987

def r37102 : Route 9 := (fun mask => (mask,id))

def c37102 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37102 : Upper (D 6) (R 6) [34,129,72,5,320] 13 := by
  apply FastRouting.sound _ _ [34,129,72,5,320] 13 (by decide) (choices 1) [2,4,16] r37102 c37102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21988
  · exact u21989
  · exact u21990

def r37103 : Route 9 := (fun mask => (mask,id))

def c37103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37103 : Upper (D 6) (R 6) [34,129,72,6,5] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,5] 13 (by decide) (choices 1) [16,64,256] r37103 c37103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21991
  · exact u21992
  · exact u21993

def b37104 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 76 14 49 372 340 468 340), lower := (rows 35 131 76 14 49 32 64 128 256), losses := [] }

theorem u37104 : Upper (D 6) (R 6) [34,129,72,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37105 : Route 9 := (fun mask => (mask,id))

def c37105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37105 : Upper (D 6) (R 6) [34,129,72,6,36] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,36] 13 (by decide) (choices 1) [1,16,64,256] r37105 c37105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21994
  · exact u21995
  · exact u21996
  · exact u21997

def r37106 : Route 9 := (fun mask => (mask,id))

def c37106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37106 : Upper (D 6) (R 6) [34,129,72,6,65] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,65] 13 (by decide) (choices 1) [4,16,256] r37106 c37106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21998
  · exact u21999
  · exact u22000

def b37107 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 14 84 305 369 433 305), lower := (rows 35 131 76 14 84 32 64 128 256), losses := [] }

theorem u37107 : Upper (D 6) (R 6) [34,129,72,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37108 : Route 9 := (fun mask => (mask,id))

def c37108 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37108 : Upper (D 6) (R 6) [34,129,72,6,96] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,96] 13 (by decide) (choices 1) [1,4,16,256] r37108 c37108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22001
  · exact u22002
  · exact u22003
  · exact u22004

def r37109 : Route 9 := (fun mask => (mask,id))

def c37109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37109 : Upper (D 6) (R 6) [34,129,72,6,257] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,257] 13 (by decide) (choices 1) [4,16,64] r37109 c37109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22005
  · exact u22006
  · exact u22007

def r37110 : Route 9 := (fun mask => (mask,id))

def c37110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37110 : Upper (D 6) (R 6) [34,129,72,6,260] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,260] 13 (by decide) (choices 1) [1,16,64] r37110 c37110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22008
  · exact u22009
  · exact u22010

def r37111 : Route 9 := (fun mask => (mask,id))

def c37111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37111 : Upper (D 6) (R 6) [34,129,72,6,288] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,288] 13 (by decide) (choices 1) [1,4,16,64] r37111 c37111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22011
  · exact u22012
  · exact u22013
  · exact u22014

def r37112 : Route 9 := (fun mask => (mask,id))

def c37112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37112 : Upper (D 6) (R 6) [34,129,72,6,320] 13 := by
  apply FastRouting.sound _ _ [34,129,72,6,320] 13 (by decide) (choices 1) [1,4,16] r37112 c37112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22015
  · exact u22016
  · exact u22017

def r37113 : Route 9 := (fun mask => (mask,id))

def c37113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37113 : Upper (D 6) (R 6) [34,129,72,17,6] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,6] 13 (by decide) (choices 1) [4,64,256] r37113 c37113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22018
  · exact u22019
  · exact u22020

def b37114 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 76 25 50 356 324 452 324), lower := (rows 35 131 76 25 50 32 64 128 256), losses := [] }

theorem u37114 : Upper (D 6) (R 6) [34,129,72,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37115 : Route 9 := (fun mask => (mask,id))

def c37115 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37115 : Upper (D 6) (R 6) [34,129,72,17,36] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,36] 13 (by decide) (choices 1) [2,4,64,256] r37115 c37115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22021
  · exact u22022
  · exact u22023
  · exact u22024

def b37116 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 356, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 76 25 82 292 356 420 292), lower := (rows 35 131 76 25 82 32 64 128 256), losses := [] }

theorem u37116 : Upper (D 6) (R 6) [34,129,72,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37117 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 25 84 294 358 422 294), lower := (rows 35 131 76 25 84 32 64 128 256), losses := [] }

theorem u37117 : Upper (D 6) (R 6) [34,129,72,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37118 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,6),(1,5),(1,6)], upper := (rows 35 131 76 25 112 294 326 390 262), lower := (rows 35 131 76 25 112 32 64 128 256), losses := [] }

theorem u37118 : Upper (D 6) (R 6) [34,129,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37119 : Route 9 := (fun mask => (mask,id))

def c37119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37119 : Upper (D 6) (R 6) [34,129,72,17,258] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,258] 13 (by decide) (choices 1) [4,64] r37119 c37119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22025
  · exact u22026

def r37120 : Route 9 := (fun mask => (mask,id))

def c37120 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37120 : Upper (D 6) (R 6) [34,129,72,17,260] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,260] 13 (by decide) (choices 1) [2,4,64] r37120 c37120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22027
  · exact u22028
  · exact u22029

def r37121 : Route 9 := (fun mask => (mask,id))

def c37121 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37121 : Upper (D 6) (R 6) [34,129,72,17,288] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,288] 13 (by decide) (choices 1) [2,4,64] r37121 c37121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22030
  · exact u22031
  · exact u22032

def r37122 : Route 9 := (fun mask => (mask,id))

def c37122 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37122 : Upper (D 6) (R 6) [34,129,72,17,320] 13 := by
  apply FastRouting.sound _ _ [34,129,72,17,320] 13 (by decide) (choices 1) [2,4] r37122 c37122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22033
  · exact u22034

def r37123 : Route 9 := (fun mask => (mask,id))

def c37123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37123 : Upper (D 6) (R 6) [34,129,72,18,5] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,5] 13 (by decide) (choices 1) [4,64,256] r37123 c37123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22035
  · exact u22036
  · exact u22037

def b37124 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 76 26 49 356 324 452 324), lower := (rows 35 131 76 26 49 32 64 128 256), losses := [] }

theorem u37124 : Upper (D 6) (R 6) [34,129,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37125 : Route 9 := (fun mask => (mask,id))

def c37125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37125 : Upper (D 6) (R 6) [34,129,72,18,36] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,36] 13 (by decide) (choices 1) [1,4,64,256] r37125 c37125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22038
  · exact u22039
  · exact u22040
  · exact u22041

def b37126 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 356, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 76 26 81 292 356 420 292), lower := (rows 35 131 76 26 81 32 64 128 256), losses := [] }

theorem u37126 : Upper (D 6) (R 6) [34,129,72,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37127 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 26 84 293 357 421 293), lower := (rows 35 131 76 26 84 32 64 128 256), losses := [] }

theorem u37127 : Upper (D 6) (R 6) [34,129,72,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37128 : Route 9 := (fun mask => (mask,id))

def c37128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37128 : Upper (D 6) (R 6) [34,129,72,18,96] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,96] 13 (by decide) (choices 1) [1,4,256] r37128 c37128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22042
  · exact u22043
  · exact u22044

def r37129 : Route 9 := (fun mask => (mask,id))

def c37129 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37129 : Upper (D 6) (R 6) [34,129,72,18,257] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,257] 13 (by decide) (choices 1) [4,64] r37129 c37129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22045
  · exact u22046

def r37130 : Route 9 := (fun mask => (mask,id))

def c37130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37130 : Upper (D 6) (R 6) [34,129,72,18,260] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,260] 13 (by decide) (choices 1) [1,4,64] r37130 c37130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22047
  · exact u22048
  · exact u22049

def r37131 : Route 9 := (fun mask => (mask,id))

def c37131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37131 : Upper (D 6) (R 6) [34,129,72,18,288] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,288] 13 (by decide) (choices 1) [1,4,64] r37131 c37131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22050
  · exact u22051
  · exact u22052

def r37132 : Route 9 := (fun mask => (mask,id))

def c37132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37132 : Upper (D 6) (R 6) [34,129,72,18,320] 13 := by
  apply FastRouting.sound _ _ [34,129,72,18,320] 13 (by decide) (choices 1) [1,4] r37132 c37132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22053
  · exact u22054

def b37133 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 28 19 356 356 484 356), lower := (rows 35 131 76 28 19 32 64 128 256), losses := [] }

theorem u37133 : Upper (D 6) (R 6) [34,129,72,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37134 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 76 28 21 354 354 482 354), lower := (rows 35 131 76 28 21 32 64 128 256), losses := [] }

theorem u37134 : Upper (D 6) (R 6) [34,129,72,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37135 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 76 28 22 353 353 481 353), lower := (rows 35 131 76 28 22 32 64 128 256), losses := [] }

theorem u37135 : Upper (D 6) (R 6) [34,129,72,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37136 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 76 28 49 358 326 454 326), lower := (rows 35 131 76 28 49 32 64 128 256), losses := [] }

theorem u37136 : Upper (D 6) (R 6) [34,129,72,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37137 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 76 28 50 357 325 453 325), lower := (rows 35 131 76 28 50 32 64 128 256), losses := [] }

theorem u37137 : Upper (D 6) (R 6) [34,129,72,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37138 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 76 28 52 355 323 451 323), lower := (rows 35 131 76 28 52 32 64 128 256), losses := [] }

theorem u37138 : Upper (D 6) (R 6) [34,129,72,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37139 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 28 81 294 358 422 294), lower := (rows 35 131 76 28 81 32 64 128 256), losses := [] }

theorem u37139 : Upper (D 6) (R 6) [34,129,72,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u37139
end Delivery.IrregularNine14.P06
