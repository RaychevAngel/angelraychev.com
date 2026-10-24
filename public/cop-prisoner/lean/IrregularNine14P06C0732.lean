import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0715
import IrregularNine14P06C0716
import IrregularNine14P06C0717
import IrregularNine14P06C0718
import IrregularNine14P06C0719
import IrregularNine14P06C0720
import IrregularNine14P06C0721
import IrregularNine14P06C0722
import IrregularNine14P06C0723
import IrregularNine14P06C0724
import IrregularNine14P06C0725

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r43920 : Route 9 := (fun mask => (mask,id))

def c43920 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43920 : Upper (D 6) (R 6) [34,129,320] 13 := by
  apply FastRouting.sound _ _ [34,129,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43920 c43920
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42910
  · exact u42911
  · exact u42912
  · exact u42913
  · exact u42914
  · exact u42915
  · exact u42916
  · exact u42917
  · exact u42918
  · exact u42919
  · exact u42920
  · exact u42921
  · exact u42922
  · exact u42923
  · exact u42924

def r43921 : Route 9 := (fun mask => (mask,id))

def c43921 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43921 : Upper (D 6) (R 6) [34,132,40] 13 := by
  apply FastRouting.sound _ _ [34,132,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43921 c43921
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42925
  · exact u42926
  · exact u42927
  · exact u42928
  · exact u42929
  · exact u42930
  · exact u42931
  · exact u42932
  · exact u42933
  · exact u42934
  · exact u42935
  · exact u42936
  · exact u42937
  · exact u42938
  · exact u42939

def r43922 : Route 9 := (fun mask => (mask,id))

def c43922 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43922 : Upper (D 6) (R 6) [34,132,72] 13 := by
  apply FastRouting.sound _ _ [34,132,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43922 c43922
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42940
  · exact u42941
  · exact u42942
  · exact u42943
  · exact u42944
  · exact u42945
  · exact u42946
  · exact u42947
  · exact u42948
  · exact u42949
  · exact u42950
  · exact u42951
  · exact u42952
  · exact u42953
  · exact u42954
  · exact u42955
  · exact u42956
  · exact u42957
  · exact u42958
  · exact u42959
  · exact u42960

def r43923 : Route 9 := (fun mask => (mask,id))

def c43923 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43923 : Upper (D 6) (R 6) [34,132,96] 13 := by
  apply FastRouting.sound _ _ [34,132,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43923 c43923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42961
  · exact u42962
  · exact u42963
  · exact u42964
  · exact u42965
  · exact u42966
  · exact u42967
  · exact u42968
  · exact u42969
  · exact u42970
  · exact u42971
  · exact u42972
  · exact u42973
  · exact u42974
  · exact u42975

def r43924 : Route 9 := (fun mask => (mask,id))

def c43924 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43924 : Upper (D 6) (R 6) [34,132,257] 13 := by
  apply FastRouting.sound _ _ [34,132,257] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43924 c43924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42976
  · exact u42977
  · exact u42978
  · exact u42979
  · exact u42980
  · exact u42981
  · exact u42982
  · exact u42983
  · exact u42984
  · exact u42985
  · exact u42986
  · exact u42987
  · exact u42988
  · exact u42989
  · exact u42990

def r43925 : Route 9 := (fun mask => (mask,id))

def c43925 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43925 : Upper (D 6) (R 6) [34,132,258] 13 := by
  apply FastRouting.sound _ _ [34,132,258] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] r43925 c43925
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42991
  · exact u42992
  · exact u42993
  · exact u42994
  · exact u42995
  · exact u42996
  · exact u42997
  · exact u42998
  · exact u42999
  · exact u43000

def r43926 : Route 9 := (fun mask => (mask,id))

def c43926 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43926 : Upper (D 6) (R 6) [34,132,264] 13 := by
  apply FastRouting.sound _ _ [34,132,264] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43926 c43926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43001
  · exact u43002
  · exact u43003
  · exact u43004
  · exact u43005
  · exact u43006
  · exact u43007
  · exact u43008
  · exact u43009
  · exact u43010
  · exact u43011
  · exact u43012
  · exact u43013
  · exact u43014
  · exact u43015

def r43927 : Route 9 := (fun mask => (mask,id))

def c43927 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43927 : Upper (D 6) (R 6) [34,132,288] 13 := by
  apply FastRouting.sound _ _ [34,132,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43927 c43927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43016
  · exact u43017
  · exact u43018
  · exact u43019
  · exact u43020
  · exact u43021
  · exact u43022
  · exact u43023
  · exact u43024
  · exact u43025

def r43928 : Route 9 := (fun mask => (mask,id))

def c43928 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43928 : Upper (D 6) (R 6) [34,132,320] 13 := by
  apply FastRouting.sound _ _ [34,132,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43928 c43928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43026
  · exact u43027
  · exact u43028
  · exact u43029
  · exact u43030
  · exact u43031
  · exact u43032
  · exact u43033
  · exact u43034
  · exact u43035
  · exact u43036
  · exact u43037
  · exact u43038
  · exact u43039
  · exact u43040

def b43929 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 64 },{ cop := 2, region := 1, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 35 138 38 349 341 373 341 469 341), lower := (rows 35 138 38 8 16 32 64 128 256), losses := [] }

theorem u43929 : Upper (D 6) (R 6) [34,136,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43930 : Route 9 := (fun mask => (mask,id))

def c43930 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 18 => 4 | 34 => 5 | 130 => 7 | 20 => 4 | 36 => 5 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43930 : Upper (D 6) (R 6) [34,136,48] 13 := by
  apply FastRouting.sound _ _ [34,136,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43930 c43930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43041
  · exact u43042
  · exact u43043
  · exact u43044
  · exact u43045
  · exact u43046
  · exact u43047
  · exact u43048
  · exact u43049
  · exact u43050

theorem m43931_20 : Upper (D 6) (R 6) [34,136,66,20] 13 :=
  permutation_upper _ _ _ [34,136,66,17] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43052

theorem m43931_65 : Upper (D 6) (R 6) [34,136,66,65] 13 :=
  permutation_upper _ _ _ [34,136,66,36] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43054

theorem m43931_68 : Upper (D 6) (R 6) [34,136,66,68] 13 :=
  permutation_upper _ _ _ [34,136,66,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43053

theorem m43931_80 : Upper (D 6) (R 6) [34,136,66,80] 13 :=
  permutation_upper _ _ _ [34,136,66,48] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43055

theorem m43931_260 : Upper (D 6) (R 6) [34,136,66,260] 13 :=
  permutation_upper _ _ _ [34,136,66,257] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43057

theorem m43931_320 : Upper (D 6) (R 6) [34,136,66,320] 13 :=
  permutation_upper _ _ _ [34,136,66,288] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43059

def r43931 : Route 9 := (fun mask => (mask,id))

def c43931 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43931 : Upper (D 6) (R 6) [34,136,66] 13 := by
  apply FastRouting.sound _ _ [34,136,66] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r43931 c43931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43051
  · exact u43052
  · exact m43931_20
  · exact u43053
  · exact u43054
  · exact u43055
  · exact m43931_65
  · exact m43931_68
  · exact m43931_80
  · exact u43056
  · exact u43057
  · exact m43931_260
  · exact u43058
  · exact u43059
  · exact m43931_320

def r43932 : Route 9 := (fun mask => (mask,id))

def c43932 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43932 : Upper (D 6) (R 6) [34,136,80] 13 := by
  apply FastRouting.sound _ _ [34,136,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43932 c43932
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43060
  · exact u43061
  · exact u43062
  · exact u43063
  · exact u43064
  · exact u43065
  · exact u43066
  · exact u43067
  · exact u43068
  · exact u43069
  · exact u43070
  · exact u43071
  · exact u43072
  · exact u43073
  · exact u43074

def r43933 : Route 9 := (fun mask => (mask,id))

def c43933 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43933 : Upper (D 6) (R 6) [34,136,96] 13 := by
  apply FastRouting.sound _ _ [34,136,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43933 c43933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43075
  · exact u43076
  · exact u43077
  · exact u43078
  · exact u43079
  · exact u43080
  · exact u43081
  · exact u43082
  · exact u43083
  · exact u43084
  · exact u43085
  · exact u43086
  · exact u43087
  · exact u43088
  · exact u43089

def r43934 : Route 9 := (fun mask => (mask,id))

def c43934 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43934 : Upper (D 6) (R 6) [34,136,257] 13 := by
  apply FastRouting.sound _ _ [34,136,257] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43934 c43934
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43090
  · exact u43091
  · exact u43092
  · exact u43093
  · exact u43094
  · exact u43095
  · exact u43096
  · exact u43097
  · exact u43098
  · exact u43099
  · exact u43100
  · exact u43101
  · exact u43102
  · exact u43103
  · exact u43104

def r43935 : Route 9 := (fun mask => (mask,id))

def c43935 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43935 : Upper (D 6) (R 6) [34,136,258] 13 := by
  apply FastRouting.sound _ _ [34,136,258] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] r43935 c43935
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43105
  · exact u43106
  · exact u43107
  · exact u43108
  · exact u43109
  · exact u43110
  · exact u43111
  · exact u43112
  · exact u43113
  · exact u43114

def r43936 : Route 9 := (fun mask => (mask,id))

def c43936 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43936 : Upper (D 6) (R 6) [34,136,272] 13 := by
  apply FastRouting.sound _ _ [34,136,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43936 c43936
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43115
  · exact u43116
  · exact u43117
  · exact u43118
  · exact u43119
  · exact u43120
  · exact u43121
  · exact u43122
  · exact u43123
  · exact u43124

def r43937 : Route 9 := (fun mask => (mask,id))

def c43937 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43937 : Upper (D 6) (R 6) [34,136,288] 13 := by
  apply FastRouting.sound _ _ [34,136,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43937 c43937
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43125
  · exact u43126
  · exact u43127
  · exact u43128
  · exact u43129
  · exact u43130
  · exact u43131
  · exact u43132
  · exact u43133
  · exact u43134

def r43938 : Route 9 := (fun mask => (mask,id))

def c43938 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43938 : Upper (D 6) (R 6) [34,136,320] 13 := by
  apply FastRouting.sound _ _ [34,136,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43938 c43938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43135
  · exact u43136
  · exact u43137
  · exact u43138
  · exact u43139
  · exact u43140
  · exact u43141
  · exact u43142
  · exact u43143
  · exact u43144
  · exact u43145
  · exact u43146
  · exact u43147
  · exact u43148
  · exact u43149

def b43939 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 162 70 349 349 381 349 477 349), lower := (rows 35 162 70 8 16 32 64 128 256), losses := [] }

theorem u43939 : Upper (D 6) (R 6) [34,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43940 : PairBound 9 := { available := 343, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 162 76 351 343 375 343 471 343), lower := (rows 35 162 76 8 16 32 64 128 256), losses := [] }

theorem u43940 : Upper (D 6) (R 6) [34,160,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43941 : PairBound 9 := { available := 95, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 162 261 95 95 127 95 223 351), lower := (rows 35 162 261 8 16 32 64 128 256), losses := [] }

theorem u43941 : Upper (D 6) (R 6) [34,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43942 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 162 262 93 93 125 93 221 349), lower := (rows 35 162 262 8 16 32 64 128 256), losses := [] }

theorem u43942 : Upper (D 6) (R 6) [34,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43943 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 162 268 95 87 119 87 215 343), lower := (rows 35 162 268 8 16 32 64 128 256), losses := [] }

theorem u43943 : Upper (D 6) (R 6) [34,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43944 : PairBound 9 := { available := 95, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 162 324 95 95 127 95 223 351), lower := (rows 35 162 324 8 16 32 64 128 256), losses := [] }

theorem u43944 : Upper (D 6) (R 6) [34,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43945 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 64 },{ cop := 2, region := 1, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 35 194 38 349 349 381 349 477 349), lower := (rows 35 194 38 8 16 32 64 128 256), losses := [] }

theorem u43945 : Upper (D 6) (R 6) [34,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43946 : Route 9 := (fun mask => (mask,id))

def c43946 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43946 : Upper (D 6) (R 6) [34,192,40] 13 := by
  apply FastRouting.sound _ _ [34,192,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43946 c43946
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43150
  · exact u43151
  · exact u43152
  · exact u43153
  · exact u43154
  · exact u43155
  · exact u43156
  · exact u43157
  · exact u43158
  · exact u43159
  · exact u43160
  · exact u43161
  · exact u43162
  · exact u43163
  · exact u43164

def r43947 : Route 9 := (fun mask => (mask,id))

def c43947 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43947 : Upper (D 6) (R 6) [34,192,72] 13 := by
  apply FastRouting.sound _ _ [34,192,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r43947 c43947
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43165
  · exact u43166
  · exact u43167
  · exact u43168
  · exact u43169
  · exact u43170
  · exact u43171
  · exact u43172
  · exact u43173
  · exact u43174
  · exact u43175
  · exact u43176
  · exact u43177
  · exact u43178
  · exact u43179

def r43948 : Route 9 := (fun mask => (mask,id))

def c43948 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43948 : Upper (D 6) (R 6) [34,192,96] 13 := by
  apply FastRouting.sound _ _ [34,192,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r43948 c43948
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43180
  · exact u43181
  · exact u43182
  · exact u43183
  · exact u43184
  · exact u43185
  · exact u43186
  · exact u43187
  · exact u43188
  · exact u43189

def r43949 : Route 9 := (fun mask => (mask,id))

def c43949 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43949 : Upper (D 6) (R 6) [34,192,257] 13 := by
  apply FastRouting.sound _ _ [34,192,257] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43949 c43949
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43190
  · exact u43191
  · exact u43192
  · exact u43193
  · exact u43194
  · exact u43195
  · exact u43196
  · exact u43197
  · exact u43198
  · exact u43199
  · exact u43200
  · exact u43201
  · exact u43202
  · exact u43203
  · exact u43204

def r43950 : Route 9 := (fun mask => (mask,id))

def c43950 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43950 : Upper (D 6) (R 6) [34,192,258] 13 := by
  apply FastRouting.sound _ _ [34,192,258] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] r43950 c43950
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43205
  · exact u43206
  · exact u43207
  · exact u43208
  · exact u43209
  · exact u43210
  · exact u43211
  · exact u43212
  · exact u43213
  · exact u43214

def r43951 : Route 9 := (fun mask => (mask,id))

def c43951 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43951 : Upper (D 6) (R 6) [34,192,264] 13 := by
  apply FastRouting.sound _ _ [34,192,264] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43951 c43951
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43215
  · exact u43216
  · exact u43217
  · exact u43218
  · exact u43219
  · exact u43220
  · exact u43221
  · exact u43222
  · exact u43223
  · exact u43224
  · exact u43225
  · exact u43226
  · exact u43227
  · exact u43228
  · exact u43229

def r43952 : Route 9 := (fun mask => (mask,id))

def c43952 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43952 : Upper (D 6) (R 6) [34,192,288] 13 := by
  apply FastRouting.sound _ _ [34,192,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43952 c43952
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43230
  · exact u43231
  · exact u43232
  · exact u43233
  · exact u43234
  · exact u43235
  · exact u43236
  · exact u43237
  · exact u43238
  · exact u43239

def r43953 : Route 9 := (fun mask => (mask,id))

def c43953 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43953 : Upper (D 6) (R 6) [34,192,320] 13 := by
  apply FastRouting.sound _ _ [34,192,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r43953 c43953
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43240
  · exact u43241
  · exact u43242
  · exact u43243
  · exact u43244
  · exact u43245
  · exact u43246
  · exact u43247
  · exact u43248
  · exact u43249

def b43954 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 64 },{ cop := 2, region := 1, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 35 386 38 93 93 125 93 221 349), lower := (rows 35 386 38 8 16 32 64 128 256), losses := [] }

theorem u43954 : Upper (D 6) (R 6) [34,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43955 : Route 9 := (fun mask => (mask,id))

def c43955 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43955 : Upper (D 6) (R 6) [34,384,40] 13 := by
  apply FastRouting.sound _ _ [34,384,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43955 c43955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43250
  · exact u43251
  · exact u43252
  · exact u43253
  · exact u43254
  · exact u43255
  · exact u43256
  · exact u43257
  · exact u43258
  · exact u43259

theorem m43956_20 : Upper (D 6) (R 6) [34,384,66,20] 13 :=
  permutation_upper _ _ _ [34,384,66,17] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43261

theorem m43956_65 : Upper (D 6) (R 6) [34,384,66,65] 13 :=
  permutation_upper _ _ _ [34,384,66,36] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43263

theorem m43956_68 : Upper (D 6) (R 6) [34,384,66,68] 13 :=
  permutation_upper _ _ _ [34,384,66,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43262

theorem m43956_80 : Upper (D 6) (R 6) [34,384,66,80] 13 :=
  permutation_upper _ _ _ [34,384,66,48] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43264

def r43956 : Route 9 := (fun mask => (mask,id))

def c43956 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43956 : Upper (D 6) (R 6) [34,384,66] 13 := by
  apply FastRouting.sound _ _ [34,384,66] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96] r43956 c43956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43260
  · exact u43261
  · exact m43956_20
  · exact u43262
  · exact u43263
  · exact u43264
  · exact m43956_65
  · exact m43956_68
  · exact m43956_80
  · exact u43265

def r43957 : Route 9 := (fun mask => (mask,id))

def c43957 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43957 : Upper (D 6) (R 6) [34,384,72] 13 := by
  apply FastRouting.sound _ _ [34,384,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43957 c43957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43266
  · exact u43267
  · exact u43268
  · exact u43269
  · exact u43270
  · exact u43271
  · exact u43272
  · exact u43273
  · exact u43274
  · exact u43275
  · exact u43276
  · exact u43277
  · exact u43278
  · exact u43279
  · exact u43280

def r43958 : Route 9 := (fun mask => (mask,id))

def c43958 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43958 : Upper (D 6) (R 6) [34,384,96] 13 := by
  apply FastRouting.sound _ _ [34,384,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43958 c43958
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43281
  · exact u43282
  · exact u43283
  · exact u43284
  · exact u43285
  · exact u43286
  · exact u43287
  · exact u43288
  · exact u43289
  · exact u43290

def r43959 : Route 9 := (fun mask => (mask,id))

def c43959 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 18 => 4 | 34 => 5 | 130 => 7 | 20 => 4 | 36 => 5 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43959 : Upper (D 6) (R 6) [40,48,129] 13 := by
  apply FastRouting.sound _ _ [40,48,129] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43959 c43959
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43291
  · exact u43292
  · exact u43293
  · exact u43294
  · exact u43295
  · exact u43296
  · exact u43297
  · exact u43298
  · exact u43299
  · exact u43300

def r43960 : Route 9 := (fun mask => (mask,id))

def c43960 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 18 => 4 | 34 => 5 | 130 => 7 | 20 => 4 | 36 => 5 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43960 : Upper (D 6) (R 6) [40,48,192] 13 := by
  apply FastRouting.sound _ _ [40,48,192] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43960 c43960
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43301
  · exact u43302
  · exact u43303
  · exact u43304
  · exact u43305
  · exact u43306
  · exact u43307
  · exact u43308
  · exact u43309
  · exact u43310

def r43961 : Route 9 := (fun mask => (mask,id))

def c43961 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 257 => 8 | 18 => 4 | 34 => 5 | 130 => 7 | 258 => 8 | 20 => 4 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43961 : Upper (D 6) (R 6) [40,48,384] 13 := by
  apply FastRouting.sound _ _ [40,48,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43961 c43961
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43311
  · exact u43312
  · exact u43313
  · exact u43314
  · exact u43315
  · exact u43316

def r43962 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43962 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43962 : Upper (D 6) (R 6) [40,80,96] 13 := by
  apply FastRouting.sound _ _ [40,80,96] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r43962 c43962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43317
  · exact u43318
  · exact u43319
  · exact u43320
  · exact u43321
  · exact u43322
  · exact u43323

def r43963 : Route 9 := (fun mask => (mask,id))

def c43963 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43963 : Upper (D 6) (R 6) [40,80,129] 13 := by
  apply FastRouting.sound _ _ [40,80,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43963 c43963
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43324
  · exact u43325
  · exact u43326
  · exact u43327
  · exact u43328
  · exact u43329
  · exact u43330
  · exact u43331
  · exact u43332
  · exact u43333
  · exact u43334
  · exact u43335
  · exact u43336
  · exact u43337
  · exact u43338

def r43964 : Route 9 := (fun mask => (mask,id))

def c43964 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 18 => 4 | 34 => 5 | 130 => 7 | 20 => 4 | 36 => 5 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43964 : Upper (D 6) (R 6) [40,80,160] 13 := by
  apply FastRouting.sound _ _ [40,80,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43964 c43964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43339
  · exact u43340
  · exact u43341
  · exact u43342
  · exact u43343
  · exact u43344
  · exact u43345
  · exact u43346
  · exact u43347
  · exact u43348

def r43965 : Route 9 := (fun mask => (mask,id))

def c43965 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43965 : Upper (D 6) (R 6) [40,80,384] 13 := by
  apply FastRouting.sound _ _ [40,80,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43965 c43965
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43349
  · exact u43350
  · exact u43351
  · exact u43352
  · exact u43353
  · exact u43354
  · exact u43355
  · exact u43356
  · exact u43357
  · exact u43358

def r43966 : Route 9 := (fun mask => (mask,id))

def c43966 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43966 : Upper (D 6) (R 6) [40,96,129] 13 := by
  apply FastRouting.sound _ _ [40,96,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43966 c43966
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43359
  · exact u43360
  · exact u43361
  · exact u43362
  · exact u43363
  · exact u43364
  · exact u43365
  · exact u43366
  · exact u43367
  · exact u43368
  · exact u43369
  · exact u43370
  · exact u43371
  · exact u43372
  · exact u43373

def r43967 : Route 9 := (fun mask => (mask,id))

def c43967 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 48 => 5 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43967 : Upper (D 6) (R 6) [40,96,130] 13 := by
  apply FastRouting.sound _ _ [40,96,130] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,257,258,260,272,320] r43967 c43967
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43374
  · exact u43375
  · exact u43376
  · exact u43377
  · exact u43378
  · exact u43379
  · exact u43380
  · exact u43381
  · exact u43382
  · exact u43383
  · exact u43384
  · exact u43385
  · exact u43386
  · exact u43387
  · exact u43388

def r43968 : Route 9 := (fun mask => (mask,id))

def c43968 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 129 => 7 | 18 => 4 | 34 => 5 | 130 => 7 | 20 => 4 | 36 => 5 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43968 : Upper (D 6) (R 6) [40,96,144] 13 := by
  apply FastRouting.sound _ _ [40,96,144] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43968 c43968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43389
  · exact u43390
  · exact u43391
  · exact u43392
  · exact u43393
  · exact u43394
  · exact u43395
  · exact u43396
  · exact u43397
  · exact u43398

def r43969 : Route 9 := (fun mask => (mask,id))

def c43969 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43969 : Upper (D 6) (R 6) [40,96,192] 13 := by
  apply FastRouting.sound _ _ [40,96,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r43969 c43969
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43399
  · exact u43400
  · exact u43401
  · exact u43402
  · exact u43403
  · exact u43404
  · exact u43405
  · exact u43406
  · exact u43407
  · exact u43408

def r43970 : Route 9 := (fun mask => (mask,id))

def c43970 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43970 : Upper (D 6) (R 6) [40,96,384] 13 := by
  apply FastRouting.sound _ _ [40,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43970 c43970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43409
  · exact u43410
  · exact u43411
  · exact u43412
  · exact u43413
  · exact u43414
  · exact u43415
  · exact u43416
  · exact u43417
  · exact u43418

theorem m43971_20 : Upper (D 6) (R 6) [40,129,257,20] 13 :=
  permutation_upper _ _ _ [40,129,257,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43420

theorem m43971_36 : Upper (D 6) (R 6) [40,129,257,36] 13 :=
  permutation_upper _ _ _ [40,129,257,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43421

theorem m43971_68 : Upper (D 6) (R 6) [40,129,257,68] 13 :=
  permutation_upper _ _ _ [40,129,257,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43423

def r43971 : Route 9 := (fun mask => (mask,id))

def c43971 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43971 : Upper (D 6) (R 6) [40,129,257] 13 := by
  apply FastRouting.sound _ _ [40,129,257] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96] r43971 c43971
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43419
  · exact u43420
  · exact m43971_20
  · exact u43421
  · exact m43971_36
  · exact u43422
  · exact u43423
  · exact m43971_68
  · exact u43424
  · exact u43425

def r43972 : Route 9 := (fun mask => (mask,id))

def c43972 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43972 : Upper (D 6) (R 6) [40,129,258] 13 := by
  apply FastRouting.sound _ _ [40,129,258] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43972 c43972
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43426
  · exact u43427
  · exact u43428
  · exact u43429
  · exact u43430
  · exact u43431
  · exact u43432
  · exact u43433
  · exact u43434
  · exact u43435
  · exact u43436
  · exact u43437
  · exact u43438
  · exact u43439
  · exact u43440

def r43973 : Route 9 := (fun mask => (mask,id))

def c43973 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43973 : Upper (D 6) (R 6) [40,129,272] 13 := by
  apply FastRouting.sound _ _ [40,129,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43973 c43973
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43441
  · exact u43442
  · exact u43443
  · exact u43444
  · exact u43445
  · exact u43446
  · exact u43447
  · exact u43448
  · exact u43449
  · exact u43450

def r43974 : Route 9 := (fun mask => (mask,id))

def c43974 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43974 : Upper (D 6) (R 6) [40,129,288] 13 := by
  apply FastRouting.sound _ _ [40,129,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43974 c43974
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43451
  · exact u43452
  · exact u43453
  · exact u43454
  · exact u43455
  · exact u43456
  · exact u43457
  · exact u43458
  · exact u43459
  · exact u43460

def r43975 : Route 9 := (fun mask => (mask,id))

def c43975 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43975 : Upper (D 6) (R 6) [40,129,320] 13 := by
  apply FastRouting.sound _ _ [40,129,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43975 c43975
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43461
  · exact u43462
  · exact u43463
  · exact u43464
  · exact u43465
  · exact u43466
  · exact u43467
  · exact u43468
  · exact u43469
  · exact u43470
  · exact u43471
  · exact u43472
  · exact u43473
  · exact u43474
  · exact u43475

theorem m43976_5 : Upper (D 6) (R 6) [40,132,258,5] 13 :=
  permutation_upper _ _ _ [40,132,258,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43476

theorem m43976_20 : Upper (D 6) (R 6) [40,132,258,20] 13 :=
  permutation_upper _ _ _ [40,132,258,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43479

theorem m43976_36 : Upper (D 6) (R 6) [40,132,258,36] 13 :=
  permutation_upper _ _ _ [40,132,258,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43481

theorem m43976_68 : Upper (D 6) (R 6) [40,132,258,68] 13 :=
  permutation_upper _ _ _ [40,132,258,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43484

def r43976 : Route 9 := (fun mask => (mask,id))

def c43976 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43976 : Upper (D 6) (R 6) [40,132,258] 13 := by
  apply FastRouting.sound _ _ [40,132,258] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43976 c43976
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43476
  · exact m43976_5
  · exact u43477
  · exact u43478
  · exact u43479
  · exact m43976_20
  · exact u43480
  · exact u43481
  · exact m43976_36
  · exact u43482
  · exact u43483
  · exact u43484
  · exact m43976_68
  · exact u43485
  · exact u43486

def r43977 : Route 9 := (fun mask => (mask,id))

def c43977 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43977 : Upper (D 6) (R 6) [40,132,272] 13 := by
  apply FastRouting.sound _ _ [40,132,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43977 c43977
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43487
  · exact u43488
  · exact u43489
  · exact u43490
  · exact u43491
  · exact u43492
  · exact u43493
  · exact u43494
  · exact u43495
  · exact u43496

def r43978 : Route 9 := (fun mask => (mask,id))

def c43978 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 48 => 5 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43978 : Upper (D 6) (R 6) [40,132,288] 13 := by
  apply FastRouting.sound _ _ [40,132,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80] r43978 c43978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43497
  · exact u43498
  · exact u43499
  · exact u43500
  · exact u43501
  · exact u43502
  · exact u43503
  · exact u43504
  · exact u43505
  · exact u43506

def r43979 : Route 9 := (fun mask => (mask,id))

def c43979 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43979 : Upper (D 6) (R 6) [40,132,320] 13 := by
  apply FastRouting.sound _ _ [40,132,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96] r43979 c43979
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43507
  · exact u43508
  · exact u43509
  · exact u43510
  · exact u43511
  · exact u43512
  · exact u43513
  · exact u43514
  · exact u43515
  · exact u43516
  · exact u43517
  · exact u43518
  · exact u43519
  · exact u43520
  · exact u43521

#print axioms u43979
end Delivery.IrregularNine14.P06
