import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0716
import IrregularNine14P07C0717
import IrregularNine14P07C0718
import IrregularNine14P07C0719
import IrregularNine14P07C0720
import IrregularNine14P07C0721
import IrregularNine14P07C0722
import IrregularNine14P07C0723
import IrregularNine14P07C0724

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r44280 : Route 9 := (fun mask => (mask,id))

def c44280 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u44280 : Upper (D 7) (R 7) [36,96,72] 13 := by
  apply FastRouting.sound _ _ [36,96,72] 13 (by decide) (choices 2) [3,17,18,129,130,144,257,258,272,384] r44280 c44280
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r44281 : Route 9 := (fun mask => (mask,id))

def c44281 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44281 : Upper (D 7) (R 7) [36,96,129] 13 := by
  apply FastRouting.sound _ _ [36,96,129] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192,257,258,272,320,384] r44281 c44281
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42971
  · exact u42972
  · exact u42973
  · exact u42974
  · exact u42975
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

def r44282 : Route 9 := (fun mask => (mask,id))

def c44282 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44282 : Upper (D 7) (R 7) [36,96,130] 13 := by
  apply FastRouting.sound _ _ [36,96,130] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192,257,258,272,320,384] r44282 c44282
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u42986
  · exact u42987
  · exact u42988
  · exact u42989
  · exact u42990
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

def r44283 : Route 9 := (fun mask => (mask,id))

def c44283 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44283 : Upper (D 7) (R 7) [36,96,136] 13 := by
  apply FastRouting.sound _ _ [36,96,136] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192,257,258,272,320,384] r44283 c44283
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

def r44284 : Route 9 := (fun mask => (mask,id))

def c44284 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u44284 : Upper (D 7) (R 7) [36,96,192] 13 := by
  apply FastRouting.sound _ _ [36,96,192] 13 (by decide) (choices 2) [3,17,18,129,130,144,257,258,272,384] r44284 c44284
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

def r44285 : Route 9 := (fun mask => (mask,id))

def c44285 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44285 : Upper (D 7) (R 7) [36,96,257] 13 := by
  apply FastRouting.sound _ _ [36,96,257] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44285 c44285
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r44286 : Route 9 := (fun mask => (mask,id))

def c44286 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44286 : Upper (D 7) (R 7) [36,96,258] 13 := by
  apply FastRouting.sound _ _ [36,96,258] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44286 c44286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43036
  · exact u43037
  · exact u43038
  · exact u43039
  · exact u43040
  · exact u43041
  · exact u43042
  · exact u43043
  · exact u43044
  · exact u43045

def r44287 : Route 9 := (fun mask => (mask,id))

def c44287 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44287 : Upper (D 7) (R 7) [36,96,264] 13 := by
  apply FastRouting.sound _ _ [36,96,264] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44287 c44287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43046
  · exact u43047
  · exact u43048
  · exact u43049
  · exact u43050
  · exact u43051
  · exact u43052
  · exact u43053
  · exact u43054
  · exact u43055

def r44288 : Route 9 := (fun mask => (mask,id))

def c44288 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 80 => 6 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u44288 : Upper (D 7) (R 7) [36,96,320] 13 := by
  apply FastRouting.sound _ _ [36,96,320] 13 (by decide) (choices 2) [3,17,18,129,130,144] r44288 c44288
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43056
  · exact u43057
  · exact u43058
  · exact u43059
  · exact u43060
  · exact u43061

def r44289 : Route 9 := (fun mask => (mask,id))

def c44289 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44289 : Upper (D 7) (R 7) [36,96,384] 13 := by
  apply FastRouting.sound _ _ [36,96,384] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44289 c44289
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r44290 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44290 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44290 : Upper (D 7) (R 7) [36,192,3] 13 := by
  apply FastRouting.sound _ _ [36,192,3] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r44290 c44290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43072
  · exact u43073
  · exact u43074
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

def r44291 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44291 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44291 : Upper (D 7) (R 7) [36,192,9] 13 := by
  apply FastRouting.sound _ _ [36,192,9] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r44291 c44291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43088
  · exact u43089
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

def r44292 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44292 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u44292 : Upper (D 7) (R 7) [36,192,10] 13 := by
  apply FastRouting.sound _ _ [36,192,10] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r44292 c44292
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43104
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
  · exact u43115
  · exact u43116
  · exact u43117
  · exact u43118
  · exact u43119

def r44293 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44293 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u44293 : Upper (D 7) (R 7) [36,192,24] 13 := by
  apply FastRouting.sound _ _ [36,192,24] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r44293 c44293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43120
  · exact u43121
  · exact u43122
  · exact u43123
  · exact u43124
  · exact u43125
  · exact u43126
  · exact u43127
  · exact u43128
  · exact u43129
  · exact u43130

def b44294 : PairBound 9 := { available := 475, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 37 475 475 507 475 475 475), lower := (rows 37 194 37 8 16 32 64 128 256), losses := [] }

theorem u44294 : Upper (D 7) (R 7) [36,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44295 : PairBound 9 := { available := 475, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 194 38 475 475 507 475 475 475), lower := (rows 37 194 38 8 16 32 64 128 256), losses := [] }

theorem u44295 : Upper (D 7) (R 7) [36,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44296 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 194 44 475 467 499 467 467 467), lower := (rows 37 194 44 8 16 32 64 128 256), losses := [] }

theorem u44296 : Upper (D 7) (R 7) [36,192,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44297 : Route 9 := (fun mask => (mask,id))

def c44297 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u44297 : Upper (D 7) (R 7) [36,192,65] 13 := by
  apply FastRouting.sound _ _ [36,192,65] 13 (by decide) (choices 2) [3,17,18,33,34,48,129,130,144,160,257,258,272,288,384] r44297 c44297
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43131
  · exact u43132
  · exact u43133
  · exact u43134
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

def b44298 : PairBound 9 := { available := 443, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 441, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 194 70 443 443 443 507 443 443), lower := (rows 37 194 70 8 16 32 64 128 256), losses := [] }

theorem u44298 : Upper (D 7) (R 7) [36,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44299 : Route 9 := (fun mask => (mask,id))

def c44299 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u44299 : Upper (D 7) (R 7) [36,192,72] 13 := by
  apply FastRouting.sound _ _ [36,192,72] 13 (by decide) (choices 2) [3,17,18,33,34,48,129,130,144,160,257,258,272,288,384] r44299 c44299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43146
  · exact u43147
  · exact u43148
  · exact u43149
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

def b44300 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 194 100 411 411 443 475 411 411), lower := (rows 37 194 100 8 16 32 64 128 256), losses := [] }

theorem u44300 : Upper (D 7) (R 7) [36,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44301 : PairBound 9 := { available := 315, camps := [{ cop := 1, region := 4, targets := 33 },{ cop := 2, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 196 315 315 315 379 443 315), lower := (rows 37 194 196 8 16 32 64 128 256), losses := [] }

theorem u44301 : Upper (D 7) (R 7) [36,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44302 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44302 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44302 : Upper (D 7) (R 7) [36,192,257] 13 := by
  apply FastRouting.sound _ _ [36,192,257] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44302 c44302
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43161
  · exact u43162
  · exact u43163
  · exact u43164
  · exact u43165
  · exact u43166
  · exact u43167
  · exact u43168
  · exact u43169
  · exact u43170
  · exact u43171

def r44303 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44303 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44303 : Upper (D 7) (R 7) [36,192,258] 13 := by
  apply FastRouting.sound _ _ [36,192,258] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44303 c44303
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43172
  · exact u43173
  · exact u43174
  · exact u43175
  · exact u43176
  · exact u43177
  · exact u43178
  · exact u43179
  · exact u43180
  · exact u43181
  · exact u43182

def r44304 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44304 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44304 : Upper (D 7) (R 7) [36,192,264] 13 := by
  apply FastRouting.sound _ _ [36,192,264] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44304 c44304
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43183
  · exact u43184
  · exact u43185
  · exact u43186
  · exact u43187
  · exact u43188
  · exact u43189
  · exact u43190
  · exact u43191
  · exact u43192
  · exact u43193

def b44305 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 218, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 194 292 219 219 251 219 219 475), lower := (rows 37 194 292 8 16 32 64 128 256), losses := [] }

theorem u44305 : Upper (D 7) (R 7) [36,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44306 : Route 9 := (fun mask => (mask,id))

def c44306 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u44306 : Upper (D 7) (R 7) [36,192,320] 13 := by
  apply FastRouting.sound _ _ [36,192,320] 13 (by decide) (choices 2) [3,17,18,33,34,48,129,130,144,160] r44306 c44306
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def b44307 : PairBound 9 := { available := 250, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 1, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 37 259 7 250 250 250 250 250 506), lower := (rows 37 259 7 8 16 32 64 128 256), losses := [] }

theorem u44307 : Upper (D 7) (R 7) [36,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44308 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44308 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44308 : Upper (D 7) (R 7) [36,257,9] 13 := by
  apply FastRouting.sound _ _ [36,257,9] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r44308 c44308
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43204
  · exact u43205
  · exact u43206
  · exact u43207
  · exact u43208
  · exact u43209
  · exact u43210

def r44309 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44309 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44309 : Upper (D 7) (R 7) [36,257,10] 13 := by
  apply FastRouting.sound _ _ [36,257,10] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44309 c44309
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43211
  · exact u43212
  · exact u43213
  · exact u43214
  · exact u43215
  · exact u43216
  · exact u43217
  · exact u43218
  · exact u43219
  · exact u43220
  · exact u43221

def r44310 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44310 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44310 : Upper (D 7) (R 7) [36,257,24] 13 := by
  apply FastRouting.sound _ _ [36,257,24] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r44310 c44310
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43222
  · exact u43223
  · exact u43224
  · exact u43225
  · exact u43226
  · exact u43227
  · exact u43228

def b44311 : PairBound 9 := { available := 218, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 259 37 218 218 250 218 218 474), lower := (rows 37 259 37 8 16 32 64 128 256), losses := [] }

theorem u44311 : Upper (D 7) (R 7) [36,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44312 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 259 38 219 219 251 219 219 475), lower := (rows 37 259 38 8 16 32 64 128 256), losses := [] }

theorem u44312 : Upper (D 7) (R 7) [36,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44313 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 259 44 219 211 243 211 211 467), lower := (rows 37 259 44 8 16 32 64 128 256), losses := [] }

theorem u44313 : Upper (D 7) (R 7) [36,257,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44314 : Route 9 := (fun mask => (mask,id))

def c44314 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44314 : Upper (D 7) (R 7) [36,257,65] 13 := by
  apply FastRouting.sound _ _ [36,257,65] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] r44314 c44314
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43229
  · exact u43230
  · exact u43231
  · exact u43232
  · exact u43233
  · exact u43234
  · exact u43235
  · exact u43236
  · exact u43237
  · exact u43238

def r44315 : Route 9 := (fun mask => (mask,id))

def c44315 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44315 : Upper (D 7) (R 7) [36,257,66] 13 := by
  apply FastRouting.sound _ _ [36,257,66] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44315 c44315
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43239
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
  · exact u43250
  · exact u43251
  · exact u43252
  · exact u43253

def r44316 : Route 9 := (fun mask => (mask,id))

def c44316 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44316 : Upper (D 7) (R 7) [36,257,72] 13 := by
  apply FastRouting.sound _ _ [36,257,72] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44316 c44316
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43254
  · exact u43255
  · exact u43256
  · exact u43257
  · exact u43258
  · exact u43259
  · exact u43260
  · exact u43261
  · exact u43262
  · exact u43263
  · exact u43264
  · exact u43265
  · exact u43266
  · exact u43267
  · exact u43268

def b44317 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 259 100 219 219 251 219 219 475), lower := (rows 37 259 100 8 16 32 64 128 256), losses := [] }

theorem u44317 : Upper (D 7) (R 7) [36,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44318 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44318 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44318 : Upper (D 7) (R 7) [36,257,192] 13 := by
  apply FastRouting.sound _ _ [36,257,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44318 c44318
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r44319 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44319 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44319 : Upper (D 7) (R 7) [36,264,3] 13 := by
  apply FastRouting.sound _ _ [36,264,3] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44319 c44319
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43280
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

def r44320 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44320 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44320 : Upper (D 7) (R 7) [36,264,17] 13 := by
  apply FastRouting.sound _ _ [36,264,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r44320 c44320
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43291
  · exact u43292
  · exact u43293
  · exact u43294
  · exact u43295
  · exact u43296
  · exact u43297

def r44321 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44321 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44321 : Upper (D 7) (R 7) [36,264,18] 13 := by
  apply FastRouting.sound _ _ [36,264,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r44321 c44321
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43298
  · exact u43299
  · exact u43300
  · exact u43301
  · exact u43302
  · exact u43303
  · exact u43304

def b44322 : PairBound 9 := { available := 211, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 266 37 219 211 243 211 211 467), lower := (rows 37 266 37 8 16 32 64 128 256), losses := [] }

theorem u44322 : Upper (D 7) (R 7) [36,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44323 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 266 38 219 211 243 211 211 467), lower := (rows 37 266 38 8 16 32 64 128 256), losses := [] }

theorem u44323 : Upper (D 7) (R 7) [36,264,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44324 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 266 52 203 211 227 195 195 451), lower := (rows 37 266 52 8 16 32 64 128 256), losses := [] }

theorem u44324 : Upper (D 7) (R 7) [36,264,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44325 : Route 9 := (fun mask => (mask,id))

def c44325 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44325 : Upper (D 7) (R 7) [36,264,65] 13 := by
  apply FastRouting.sound _ _ [36,264,65] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44325 c44325
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43305
  · exact u43306
  · exact u43307
  · exact u43308
  · exact u43309
  · exact u43310
  · exact u43311
  · exact u43312
  · exact u43313
  · exact u43314
  · exact u43315
  · exact u43316
  · exact u43317
  · exact u43318
  · exact u43319

def r44326 : Route 9 := (fun mask => (mask,id))

def c44326 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44326 : Upper (D 7) (R 7) [36,264,66] 13 := by
  apply FastRouting.sound _ _ [36,264,66] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44326 c44326
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43320
  · exact u43321
  · exact u43322
  · exact u43323
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

def r44327 : Route 9 := (fun mask => (mask,id))

def c44327 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44327 : Upper (D 7) (R 7) [36,264,80] 13 := by
  apply FastRouting.sound _ _ [36,264,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r44327 c44327
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43335
  · exact u43336
  · exact u43337
  · exact u43338
  · exact u43339
  · exact u43340
  · exact u43341
  · exact u43342
  · exact u43343
  · exact u43344

def b44328 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 266 100 219 211 243 211 211 467), lower := (rows 37 266 100 8 16 32 64 128 256), losses := [] }

theorem u44328 : Upper (D 7) (R 7) [36,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44329 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44329 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44329 : Upper (D 7) (R 7) [36,264,192] 13 := by
  apply FastRouting.sound _ _ [36,264,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r44329 c44329
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43345
  · exact u43346
  · exact u43347
  · exact u43348
  · exact u43349
  · exact u43350
  · exact u43351
  · exact u43352
  · exact u43353
  · exact u43354
  · exact u43355

def b44330 : PairBound 9 := { available := 219, camps := [{ cop := 1, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 290 7 219 219 251 219 219 475), lower := (rows 37 290 7 8 16 32 64 128 256), losses := [] }

theorem u44330 : Upper (D 7) (R 7) [36,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44331 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44331 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44331 : Upper (D 7) (R 7) [36,288,9] 13 := by
  apply FastRouting.sound _ _ [36,288,9] 13 (by decide) (choices 2) [3,17,18,65,66,80,192] r44331 c44331
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43356
  · exact u43357
  · exact u43358
  · exact u43359
  · exact u43360
  · exact u43361
  · exact u43362

def r44332 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44332 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44332 : Upper (D 7) (R 7) [36,288,10] 13 := by
  apply FastRouting.sound _ _ [36,288,10] 13 (by decide) (choices 2) [3,17,18,65,66,80,192] r44332 c44332
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43363
  · exact u43364
  · exact u43365
  · exact u43366
  · exact u43367
  · exact u43368
  · exact u43369

def r44333 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44333 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 257 => 8 | 6 => 2 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44333 : Upper (D 7) (R 7) [36,288,24] 13 := by
  apply FastRouting.sound _ _ [36,288,24] 13 (by decide) (choices 2) [3,65,66,192] r44333 c44333
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u43370
  · exact u43371
  · exact u43372
  · exact u43373

def r44334 : Route 9 := (fun mask => (mask,id))

def c44334 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44334 : Upper (D 7) (R 7) [36,288,65] 13 := by
  apply FastRouting.sound _ _ [36,288,65] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44334 c44334
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r44335 : Route 9 := (fun mask => (mask,id))

def c44335 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44335 : Upper (D 7) (R 7) [36,288,66] 13 := by
  apply FastRouting.sound _ _ [36,288,66] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44335 c44335
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43384
  · exact u43385
  · exact u43386
  · exact u43387
  · exact u43388
  · exact u43389
  · exact u43390
  · exact u43391
  · exact u43392
  · exact u43393

def r44336 : Route 9 := (fun mask => (mask,id))

def c44336 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44336 : Upper (D 7) (R 7) [36,288,72] 13 := by
  apply FastRouting.sound _ _ [36,288,72] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44336 c44336
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43394
  · exact u43395
  · exact u43396
  · exact u43397
  · exact u43398
  · exact u43399
  · exact u43400
  · exact u43401
  · exact u43402
  · exact u43403

def r44337 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c44337 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44337 : Upper (D 7) (R 7) [36,288,192] 13 := by
  apply FastRouting.sound _ _ [36,288,192] 13 (by decide) (choices 2) [3,17,18,65,66,80,192] r44337 c44337
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43404
  · exact u43405
  · exact u43406
  · exact u43407
  · exact u43408
  · exact u43409
  · exact u43410

def r44338 : Route 9 := (fun mask => (mask,id))

def c44338 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44338 : Upper (D 7) (R 7) [36,320,3] 13 := by
  apply FastRouting.sound _ _ [36,320,3] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44338 c44338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43411
  · exact u43412
  · exact u43413
  · exact u43414
  · exact u43415
  · exact u43416
  · exact u43417
  · exact u43418
  · exact u43419
  · exact u43420
  · exact u43421
  · exact u43422
  · exact u43423
  · exact u43424
  · exact u43425

def r44339 : Route 9 := (fun mask => (mask,id))

def c44339 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44339 : Upper (D 7) (R 7) [36,320,9] 13 := by
  apply FastRouting.sound _ _ [36,320,9] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44339 c44339
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

#print axioms u44339
end Delivery.IrregularNine14.P07
