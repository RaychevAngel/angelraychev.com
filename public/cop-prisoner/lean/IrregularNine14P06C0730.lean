import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0699
import IrregularNine14P06C0700
import IrregularNine14P06C0701
import IrregularNine14P06C0702
import IrregularNine14P06C0703
import IrregularNine14P06C0704
import IrregularNine14P06C0705
import IrregularNine14P06C0706
import IrregularNine14P06C0707
import IrregularNine14P06C0708

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r43800 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43800 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43800 : Upper (D 6) (R 6) [10,132,257] 13 := by
  apply FastRouting.sound _ _ [10,132,257] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96] r43800 c43800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41940
  · exact u41941
  · exact u41942
  · exact u41943
  · exact u41944
  · exact u41945
  · exact u41946
  · exact u41947
  · exact u41948
  · exact u41949
  · exact u41950

def r43801 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43801 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43801 : Upper (D 6) (R 6) [10,132,258] 13 := by
  apply FastRouting.sound _ _ [10,132,258] 13 (by decide) (choices 2) [5,17,20,33,36,48,96] r43801 c43801
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41951
  · exact u41952
  · exact u41953
  · exact u41954
  · exact u41955
  · exact u41956
  · exact u41957

def r43802 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43802 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43802 : Upper (D 6) (R 6) [10,132,272] 13 := by
  apply FastRouting.sound _ _ [10,132,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43802 c43802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41958
  · exact u41959
  · exact u41960
  · exact u41961
  · exact u41962
  · exact u41963
  · exact u41964

def r43803 : Route 9 := (fun mask => (mask,id))

def c43803 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43803 : Upper (D 6) (R 6) [10,132,288] 13 := by
  apply FastRouting.sound _ _ [10,132,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43803 c43803
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41965
  · exact u41966
  · exact u41967
  · exact u41968
  · exact u41969
  · exact u41970
  · exact u41971
  · exact u41972
  · exact u41973
  · exact u41974
  · exact u41975
  · exact u41976
  · exact u41977
  · exact u41978
  · exact u41979

def r43804 : Route 9 := (fun mask => (mask,id))

def c43804 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43804 : Upper (D 6) (R 6) [10,144,33] 13 := by
  apply FastRouting.sound _ _ [10,144,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43804 c43804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41980
  · exact u41981
  · exact u41982
  · exact u41983
  · exact u41984
  · exact u41985
  · exact u41986
  · exact u41987
  · exact u41988
  · exact u41989
  · exact u41990
  · exact u41991
  · exact u41992
  · exact u41993
  · exact u41994

def r43805 : Route 9 := (fun mask => (mask,id))

def c43805 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43805 : Upper (D 6) (R 6) [10,144,34] 13 := by
  apply FastRouting.sound _ _ [10,144,34] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r43805 c43805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u41995
  · exact u41996
  · exact u41997
  · exact u41998
  · exact u41999
  · exact u42000
  · exact u42001
  · exact u42002
  · exact u42003
  · exact u42004

def r43806 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43806 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43806 : Upper (D 6) (R 6) [10,144,96] 13 := by
  apply FastRouting.sound _ _ [10,144,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r43806 c43806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42005
  · exact u42006
  · exact u42007
  · exact u42008
  · exact u42009
  · exact u42010
  · exact u42011
  · exact u42012
  · exact u42013
  · exact u42014
  · exact u42015

def r43807 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43807 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43807 : Upper (D 6) (R 6) [10,144,257] 13 := by
  apply FastRouting.sound _ _ [10,144,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43807 c43807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42016
  · exact u42017
  · exact u42018
  · exact u42019
  · exact u42020
  · exact u42021
  · exact u42022

def r43808 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43808 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43808 : Upper (D 6) (R 6) [10,144,258] 13 := by
  apply FastRouting.sound _ _ [10,144,258] 13 (by decide) (choices 2) [5,33,36,96] r43808 c43808
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u42023
  · exact u42024
  · exact u42025
  · exact u42026

def r43809 : Route 9 := (fun mask => (mask,id))

def c43809 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43809 : Upper (D 6) (R 6) [10,144,288] 13 := by
  apply FastRouting.sound _ _ [10,144,288] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43809 c43809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42027
  · exact u42028
  · exact u42029
  · exact u42030
  · exact u42031
  · exact u42032
  · exact u42033
  · exact u42034
  · exact u42035
  · exact u42036

def r43810 : Route 9 := (fun mask => (mask,id))

def c43810 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43810 : Upper (D 6) (R 6) [10,160,18] 13 := by
  apply FastRouting.sound _ _ [10,160,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r43810 c43810
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42037
  · exact u42038
  · exact u42039
  · exact u42040
  · exact u42041
  · exact u42042
  · exact u42043
  · exact u42044
  · exact u42045
  · exact u42046

def r43811 : Route 9 := (fun mask => (mask,id))

def c43811 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43811 : Upper (D 6) (R 6) [10,160,33] 13 := by
  apply FastRouting.sound _ _ [10,160,33] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43811 c43811
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42047
  · exact u42048
  · exact u42049
  · exact u42050
  · exact u42051
  · exact u42052
  · exact u42053
  · exact u42054
  · exact u42055
  · exact u42056
  · exact u42057
  · exact u42058
  · exact u42059
  · exact u42060
  · exact u42061

def b43812 : PairBound 9 := { available := 341, camps := [{ cop := 2, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 38 349 341 373 341 469 341), lower := (rows 11 162 38 8 16 32 64 128 256), losses := [] }

theorem u43812 : Upper (D 6) (R 6) [10,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43813 : Route 9 := (fun mask => (mask,id))

def c43813 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 18 => 4 | 34 => 5 | 130 => 7 | 20 => 4 | 36 => 5 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43813 : Upper (D 6) (R 6) [10,160,48] 13 := by
  apply FastRouting.sound _ _ [10,160,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43813 c43813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42062
  · exact u42063
  · exact u42064
  · exact u42065
  · exact u42066
  · exact u42067
  · exact u42068
  · exact u42069
  · exact u42070
  · exact u42071

def r43814 : Route 9 := (fun mask => (mask,id))

def c43814 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43814 : Upper (D 6) (R 6) [10,160,65] 13 := by
  apply FastRouting.sound _ _ [10,160,65] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43814 c43814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42072
  · exact u42073
  · exact u42074
  · exact u42075
  · exact u42076
  · exact u42077
  · exact u42078
  · exact u42079
  · exact u42080
  · exact u42081
  · exact u42082
  · exact u42083
  · exact u42084
  · exact u42085
  · exact u42086
  · exact u42087
  · exact u42088
  · exact u42089
  · exact u42090
  · exact u42091
  · exact u42092

def r43815 : Route 9 := (fun mask => (mask,id))

def c43815 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43815 : Upper (D 6) (R 6) [10,160,66] 13 := by
  apply FastRouting.sound _ _ [10,160,66] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r43815 c43815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42093
  · exact u42094
  · exact u42095
  · exact u42096
  · exact u42097
  · exact u42098
  · exact u42099
  · exact u42100
  · exact u42101
  · exact u42102
  · exact u42103
  · exact u42104
  · exact u42105
  · exact u42106
  · exact u42107

def r43816 : Route 9 := (fun mask => (mask,id))

def c43816 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43816 : Upper (D 6) (R 6) [10,160,80] 13 := by
  apply FastRouting.sound _ _ [10,160,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43816 c43816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42108
  · exact u42109
  · exact u42110
  · exact u42111
  · exact u42112
  · exact u42113
  · exact u42114
  · exact u42115
  · exact u42116
  · exact u42117
  · exact u42118
  · exact u42119
  · exact u42120
  · exact u42121
  · exact u42122

def r43817 : Route 9 := (fun mask => (mask,id))

def c43817 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43817 : Upper (D 6) (R 6) [10,160,96] 13 := by
  apply FastRouting.sound _ _ [10,160,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43817 c43817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42123
  · exact u42124
  · exact u42125
  · exact u42126
  · exact u42127
  · exact u42128
  · exact u42129
  · exact u42130
  · exact u42131
  · exact u42132
  · exact u42133
  · exact u42134
  · exact u42135
  · exact u42136
  · exact u42137

def r43818 : Route 9 := (fun mask => (mask,id))

def c43818 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43818 : Upper (D 6) (R 6) [10,160,257] 13 := by
  apply FastRouting.sound _ _ [10,160,257] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43818 c43818
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42138
  · exact u42139
  · exact u42140
  · exact u42141
  · exact u42142
  · exact u42143
  · exact u42144
  · exact u42145
  · exact u42146
  · exact u42147
  · exact u42148
  · exact u42149
  · exact u42150
  · exact u42151
  · exact u42152

def r43819 : Route 9 := (fun mask => (mask,id))

def c43819 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43819 : Upper (D 6) (R 6) [10,160,258] 13 := by
  apply FastRouting.sound _ _ [10,160,258] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] r43819 c43819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42153
  · exact u42154
  · exact u42155
  · exact u42156
  · exact u42157
  · exact u42158
  · exact u42159
  · exact u42160
  · exact u42161
  · exact u42162

def r43820 : Route 9 := (fun mask => (mask,id))

def c43820 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43820 : Upper (D 6) (R 6) [10,160,272] 13 := by
  apply FastRouting.sound _ _ [10,160,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43820 c43820
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42163
  · exact u42164
  · exact u42165
  · exact u42166
  · exact u42167
  · exact u42168
  · exact u42169
  · exact u42170
  · exact u42171
  · exact u42172

def r43821 : Route 9 := (fun mask => (mask,id))

def c43821 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43821 : Upper (D 6) (R 6) [10,160,288] 13 := by
  apply FastRouting.sound _ _ [10,160,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43821 c43821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42173
  · exact u42174
  · exact u42175
  · exact u42176
  · exact u42177
  · exact u42178
  · exact u42179
  · exact u42180
  · exact u42181
  · exact u42182

def r43822 : Route 9 := (fun mask => (mask,id))

def c43822 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43822 : Upper (D 6) (R 6) [10,160,320] 13 := by
  apply FastRouting.sound _ _ [10,160,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43822 c43822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42183
  · exact u42184
  · exact u42185
  · exact u42186
  · exact u42187
  · exact u42188
  · exact u42189
  · exact u42190
  · exact u42191
  · exact u42192
  · exact u42193
  · exact u42194
  · exact u42195
  · exact u42196
  · exact u42197

def r43823 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43823 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43823 : Upper (D 6) (R 6) [10,384,18] 13 := by
  apply FastRouting.sound _ _ [10,384,18] 13 (by decide) (choices 2) [5,33,36,96] r43823 c43823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u42198
  · exact u42199
  · exact u42200
  · exact u42201

def r43824 : Route 9 := (fun mask => (mask,id))

def c43824 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43824 : Upper (D 6) (R 6) [10,384,33] 13 := by
  apply FastRouting.sound _ _ [10,384,33] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43824 c43824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42202
  · exact u42203
  · exact u42204
  · exact u42205
  · exact u42206
  · exact u42207
  · exact u42208
  · exact u42209
  · exact u42210
  · exact u42211
  · exact u42212
  · exact u42213
  · exact u42214
  · exact u42215
  · exact u42216

def r43825 : Route 9 := (fun mask => (mask,id))

def c43825 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43825 : Upper (D 6) (R 6) [10,384,34] 13 := by
  apply FastRouting.sound _ _ [10,384,34] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] r43825 c43825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42217
  · exact u42218
  · exact u42219
  · exact u42220
  · exact u42221
  · exact u42222
  · exact u42223
  · exact u42224
  · exact u42225
  · exact u42226

def r43826 : Route 9 := (fun mask => (mask,id))

def c43826 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43826 : Upper (D 6) (R 6) [10,384,48] 13 := by
  apply FastRouting.sound _ _ [10,384,48] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43826 c43826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42227
  · exact u42228
  · exact u42229
  · exact u42230
  · exact u42231
  · exact u42232
  · exact u42233
  · exact u42234
  · exact u42235
  · exact u42236

def r43827 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43827 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43827 : Upper (D 6) (R 6) [10,384,96] 13 := by
  apply FastRouting.sound _ _ [10,384,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96] r43827 c43827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42237
  · exact u42238
  · exact u42239
  · exact u42240
  · exact u42241
  · exact u42242
  · exact u42243
  · exact u42244
  · exact u42245
  · exact u42246
  · exact u42247

def b43828 : PairBound 9 := { available := 454, camps := [{ cop := 1, region := 4, targets := 2 },{ cop := 1, region := 4, targets := 64 },{ cop := 2, region := 2, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 25 35 37 462 470 486 454 454 454), lower := (rows 25 35 37 8 16 32 64 128 256), losses := [] }

theorem u43828 : Upper (D 6) (R 6) [24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43829 : PairBound 9 := { available := 455, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 35 38 463 471 487 455 455 455), lower := (rows 25 35 38 8 16 32 64 128 256), losses := [] }

theorem u43829 : Upper (D 6) (R 6) [24,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43830_66 : Upper (D 6) (R 6) [24,33,65,66] 13 :=
  permutation_upper _ _ _ [24,33,65,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42250

theorem m43830_68 : Upper (D 6) (R 6) [24,33,65,68] 13 :=
  permutation_upper _ _ _ [24,33,65,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42249

theorem m43830_132 : Upper (D 6) (R 6) [24,33,65,132] 13 :=
  permutation_upper _ _ _ [24,33,65,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42252

theorem m43830_192 : Upper (D 6) (R 6) [24,33,65,192] 13 :=
  permutation_upper _ _ _ [24,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42253

def r43830 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43830 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43830 : Upper (D 6) (R 6) [24,33,65] 13 := by
  apply FastRouting.sound _ _ [24,33,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r43830 c43830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42248
  · exact u42249
  · exact u42250
  · exact m43830_66
  · exact m43830_68
  · exact u42251
  · exact u42252
  · exact m43830_132
  · exact u42253
  · exact m43830_192
  · exact u42254

def r43831 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43831 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43831 : Upper (D 6) (R 6) [24,33,66] 13 := by
  apply FastRouting.sound _ _ [24,33,66] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192,384] r43831 c43831
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42255
  · exact u42256
  · exact u42257
  · exact u42258
  · exact u42259
  · exact u42260
  · exact u42261
  · exact u42262
  · exact u42263
  · exact u42264
  · exact u42265
  · exact u42266
  · exact u42267
  · exact u42268
  · exact u42269
  · exact u42270

def r43832 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43832 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43832 : Upper (D 6) (R 6) [24,33,96] 13 := by
  apply FastRouting.sound _ _ [24,33,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r43832 c43832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42271
  · exact u42272
  · exact u42273
  · exact u42274
  · exact u42275
  · exact u42276
  · exact u42277
  · exact u42278
  · exact u42279
  · exact u42280
  · exact u42281

def r43833 : Route 9 := (fun mask => (mask,id))

def c43833 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43833 : Upper (D 6) (R 6) [24,33,129] 13 := by
  apply FastRouting.sound _ _ [24,33,129] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r43833 c43833
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42282
  · exact u42283
  · exact u42284
  · exact u42285
  · exact u42286
  · exact u42287
  · exact u42288
  · exact u42289
  · exact u42290
  · exact u42291

def r43834 : Route 9 := (fun mask => (mask,id))

def c43834 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43834 : Upper (D 6) (R 6) [24,33,130] 13 := by
  apply FastRouting.sound _ _ [24,33,130] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43834 c43834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42292
  · exact u42293
  · exact u42294
  · exact u42295
  · exact u42296
  · exact u42297
  · exact u42298
  · exact u42299
  · exact u42300
  · exact u42301
  · exact u42302
  · exact u42303
  · exact u42304
  · exact u42305
  · exact u42306

def r43835 : Route 9 := (fun mask => (mask,id))

def c43835 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 18 => 4 | 34 => 5 | 130 => 7 | 20 => 4 | 36 => 5 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43835 : Upper (D 6) (R 6) [24,33,160] 13 := by
  apply FastRouting.sound _ _ [24,33,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43835 c43835
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42307
  · exact u42308
  · exact u42309
  · exact u42310
  · exact u42311
  · exact u42312
  · exact u42313
  · exact u42314
  · exact u42315
  · exact u42316

def r43836 : Route 9 := (fun mask => (mask,id))

def c43836 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43836 : Upper (D 6) (R 6) [24,33,192] 13 := by
  apply FastRouting.sound _ _ [24,33,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43836 c43836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42317
  · exact u42318
  · exact u42319
  · exact u42320
  · exact u42321
  · exact u42322
  · exact u42323
  · exact u42324
  · exact u42325
  · exact u42326
  · exact u42327
  · exact u42328
  · exact u42329
  · exact u42330
  · exact u42331

def r43837 : Route 9 := (fun mask => (mask,id))

def c43837 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43837 : Upper (D 6) (R 6) [24,33,384] 13 := by
  apply FastRouting.sound _ _ [24,33,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43837 c43837
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42332
  · exact u42333
  · exact u42334
  · exact u42335
  · exact u42336
  · exact u42337
  · exact u42338
  · exact u42339
  · exact u42340
  · exact u42341

def b43838 : PairBound 9 := { available := 455, camps := [{ cop := 5, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 38 463 471 487 455 455 455), lower := (rows 25 38 38 8 16 32 64 128 256), losses := [] }

theorem u43838 : Upper (D 6) (R 6) [24,36,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43839_5 : Upper (D 6) (R 6) [24,36,66,5] 13 :=
  permutation_upper _ _ _ [24,36,66,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42342

theorem m43839_65 : Upper (D 6) (R 6) [24,36,66,65] 13 :=
  permutation_upper _ _ _ [24,36,66,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42344

theorem m43839_66 : Upper (D 6) (R 6) [24,36,66,66] 13 :=
  permutation_upper _ _ _ [24,36,66,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42346

theorem m43839_68 : Upper (D 6) (R 6) [24,36,66,68] 13 :=
  permutation_upper _ _ _ [24,36,66,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42345

theorem m43839_132 : Upper (D 6) (R 6) [24,36,66,132] 13 :=
  permutation_upper _ _ _ [24,36,66,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42349

theorem m43839_192 : Upper (D 6) (R 6) [24,36,66,192] 13 :=
  permutation_upper _ _ _ [24,36,66,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42350

def r43839 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43839 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43839 : Upper (D 6) (R 6) [24,36,66] 13 := by
  apply FastRouting.sound _ _ [24,36,66] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192,384] r43839 c43839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42342
  · exact m43839_5
  · exact u42343
  · exact u42344
  · exact u42345
  · exact u42346
  · exact m43839_65
  · exact m43839_66
  · exact m43839_68
  · exact u42347
  · exact u42348
  · exact u42349
  · exact m43839_132
  · exact u42350
  · exact m43839_192
  · exact u42351

def b43840 : PairBound 9 := { available := 455, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 100 463 471 487 455 455 455), lower := (rows 25 38 100 8 16 32 64 128 256), losses := [] }

theorem u43840 : Upper (D 6) (R 6) [24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43841 : Route 9 := (fun mask => (mask,id))

def c43841 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43841 : Upper (D 6) (R 6) [24,36,129] 13 := by
  apply FastRouting.sound _ _ [24,36,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43841 c43841
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42352
  · exact u42353
  · exact u42354
  · exact u42355
  · exact u42356
  · exact u42357
  · exact u42358
  · exact u42359
  · exact u42360
  · exact u42361
  · exact u42362
  · exact u42363
  · exact u42364
  · exact u42365
  · exact u42366

def r43842 : Route 9 := (fun mask => (mask,id))

def c43842 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43842 : Upper (D 6) (R 6) [24,36,130] 13 := by
  apply FastRouting.sound _ _ [24,36,130] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43842 c43842
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42367
  · exact u42368
  · exact u42369
  · exact u42370
  · exact u42371
  · exact u42372
  · exact u42373
  · exact u42374
  · exact u42375
  · exact u42376
  · exact u42377
  · exact u42378
  · exact u42379
  · exact u42380
  · exact u42381

def b43843 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 164 335 343 359 327 455 327), lower := (rows 25 38 164 8 16 32 64 128 256), losses := [] }

theorem u43843 : Upper (D 6) (R 6) [24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43844 : Route 9 := (fun mask => (mask,id))

def c43844 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43844 : Upper (D 6) (R 6) [24,36,192] 13 := by
  apply FastRouting.sound _ _ [24,36,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43844 c43844
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42382
  · exact u42383
  · exact u42384
  · exact u42385
  · exact u42386
  · exact u42387
  · exact u42388
  · exact u42389
  · exact u42390
  · exact u42391
  · exact u42392
  · exact u42393
  · exact u42394
  · exact u42395
  · exact u42396

def r43845 : Route 9 := (fun mask => (mask,id))

def c43845 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43845 : Upper (D 6) (R 6) [24,36,384] 13 := by
  apply FastRouting.sound _ _ [24,36,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43845 c43845
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42397
  · exact u42398
  · exact u42399
  · exact u42400
  · exact u42401
  · exact u42402
  · exact u42403
  · exact u42404
  · exact u42405
  · exact u42406

def b43846 : PairBound 9 := { available := 391, camps := [{ cop := 1, region := 4, targets := 1 },{ cop := 1, region := 4, targets := 2 },{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 98 100 399 407 423 455 391 391), lower := (rows 25 98 100 8 16 32 64 128 256), losses := [] }

theorem u43846 : Upper (D 6) (R 6) [24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43847 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43847 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43847 : Upper (D 6) (R 6) [24,96,129] 13 := by
  apply FastRouting.sound _ _ [24,96,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r43847 c43847
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42407
  · exact u42408
  · exact u42409
  · exact u42410
  · exact u42411
  · exact u42412
  · exact u42413
  · exact u42414
  · exact u42415
  · exact u42416
  · exact u42417

def r43848 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43848 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43848 : Upper (D 6) (R 6) [24,96,130] 13 := by
  apply FastRouting.sound _ _ [24,96,130] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r43848 c43848
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42418
  · exact u42419
  · exact u42420
  · exact u42421
  · exact u42422
  · exact u42423
  · exact u42424
  · exact u42425
  · exact u42426
  · exact u42427
  · exact u42428

def r43849 : Route 9 := (fun mask => (mask,id))

def c43849 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 18 => 4 | 34 => 5 | 130 => 7 | 20 => 4 | 36 => 5 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43849 : Upper (D 6) (R 6) [24,96,160] 13 := by
  apply FastRouting.sound _ _ [24,96,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43849 c43849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42429
  · exact u42430
  · exact u42431
  · exact u42432
  · exact u42433
  · exact u42434
  · exact u42435
  · exact u42436
  · exact u42437
  · exact u42438

def r43850 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43850 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43850 : Upper (D 6) (R 6) [24,96,384] 13 := by
  apply FastRouting.sound _ _ [24,96,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43850 c43850
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42439
  · exact u42440
  · exact u42441
  · exact u42442
  · exact u42443
  · exact u42444
  · exact u42445

theorem m43851_36 : Upper (D 6) (R 6) [24,129,257,36] 13 :=
  permutation_upper _ _ _ [24,129,257,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42447

def r43851 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43851 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43851 : Upper (D 6) (R 6) [24,129,257] 13 := by
  apply FastRouting.sound _ _ [24,129,257] 13 (by decide) (choices 2) [6,34,36,96] r43851 c43851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u42446
  · exact u42447
  · exact m43851_36
  · exact u42448

def r43852 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43852 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43852 : Upper (D 6) (R 6) [24,129,258] 13 := by
  apply FastRouting.sound _ _ [24,129,258] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43852 c43852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42449
  · exact u42450
  · exact u42451
  · exact u42452
  · exact u42453
  · exact u42454
  · exact u42455

def r43853 : Route 9 := (fun mask => (mask,id))

def c43853 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43853 : Upper (D 6) (R 6) [24,129,288] 13 := by
  apply FastRouting.sound _ _ [24,129,288] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43853 c43853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42456
  · exact u42457
  · exact u42458
  · exact u42459
  · exact u42460
  · exact u42461
  · exact u42462
  · exact u42463
  · exact u42464
  · exact u42465

theorem m43854_5 : Upper (D 6) (R 6) [24,132,258,5] 13 :=
  permutation_upper _ _ _ [24,132,258,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42466

theorem m43854_36 : Upper (D 6) (R 6) [24,132,258,36] 13 :=
  permutation_upper _ _ _ [24,132,258,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42469

def r43854 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43854 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43854 : Upper (D 6) (R 6) [24,132,258] 13 := by
  apply FastRouting.sound _ _ [24,132,258] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43854 c43854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42466
  · exact m43854_5
  · exact u42467
  · exact u42468
  · exact u42469
  · exact m43854_36
  · exact u42470

def r43855 : Route 9 := (fun mask => (mask,id))

def c43855 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43855 : Upper (D 6) (R 6) [24,132,288] 13 := by
  apply FastRouting.sound _ _ [24,132,288] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43855 c43855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42471
  · exact u42472
  · exact u42473
  · exact u42474
  · exact u42475
  · exact u42476
  · exact u42477
  · exact u42478
  · exact u42479
  · exact u42480

theorem m43856_5 : Upper (D 6) (R 6) [24,160,288,5] 13 :=
  permutation_upper _ _ _ [24,160,288,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42481

theorem m43856_68 : Upper (D 6) (R 6) [24,160,288,68] 13 :=
  permutation_upper _ _ _ [24,160,288,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42484

def r43856 : Route 9 := (fun mask => (mask,id))

def c43856 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 257 => 8 | 18 => 4 | 34 => 5 | 130 => 7 | 258 => 8 | 20 => 4 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43856 : Upper (D 6) (R 6) [24,160,288] 13 := by
  apply FastRouting.sound _ _ [24,160,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43856 c43856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42481
  · exact m43856_5
  · exact u42482
  · exact u42483
  · exact u42484
  · exact m43856_68

theorem m43857_5 : Upper (D 6) (R 6) [24,160,320,5] 13 :=
  permutation_upper _ _ _ [24,160,320,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42485

theorem m43857_65 : Upper (D 6) (R 6) [24,160,320,65] 13 :=
  permutation_upper _ _ _ [24,160,320,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42487

theorem m43857_66 : Upper (D 6) (R 6) [24,160,320,66] 13 :=
  permutation_upper _ _ _ [24,160,320,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42489

theorem m43857_68 : Upper (D 6) (R 6) [24,160,320,68] 13 :=
  permutation_upper _ _ _ [24,160,320,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u42488

def r43857 : Route 9 := (fun mask => (mask,id))

def c43857 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43857 : Upper (D 6) (R 6) [24,160,320] 13 := by
  apply FastRouting.sound _ _ [24,160,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43857 c43857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42485
  · exact m43857_5
  · exact u42486
  · exact u42487
  · exact u42488
  · exact u42489
  · exact m43857_65
  · exact m43857_66
  · exact m43857_68
  · exact u42490

def b43858 : PairBound 9 := { available := 478, camps := [{ cop := 5, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 35 69 478 478 510 478 478 478), lower := (rows 35 35 69 8 16 32 64 128 256), losses := [] }

theorem u43858 : Upper (D 6) (R 6) [34,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43859 : PairBound 9 := { available := 471, camps := [{ cop := 5, region := 3, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 35 76 479 471 503 471 471 471), lower := (rows 35 35 76 8 16 32 64 128 256), losses := [] }

theorem u43859 : Upper (D 6) (R 6) [34,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u43859
end Delivery.IrregularNine14.P06
