import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0500
import IrregularNine14P06C0501
import IrregularNine14P06C0502
import IrregularNine14P06C0503
import IrregularNine14P06C0504

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41160 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 37 13 498 482 482 482 482), lower := (rows 11 22 37 13 16 32 64 128 256), losses := [] }

theorem u41160 : Upper (D 6) (R 6) [10,20,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41161 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 37 14 497 481 481 481 481), lower := (rows 11 22 37 14 16 32 64 128 256), losses := [] }

theorem u41161 : Upper (D 6) (R 6) [10,20,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41162 : PairBound 9 := { available := 454, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 8, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 22 37 41 470 486 454 454 454), lower := (rows 11 22 37 41 16 32 64 128 256), losses := [] }

theorem u41162 : Upper (D 6) (R 6) [10,20,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41163 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 11 22 37 42 469 485 453 453 453), lower := (rows 11 22 37 42 16 32 64 128 256), losses := [] }

theorem u41163 : Upper (D 6) (R 6) [10,20,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41164 : PairBound 9 := { available := 451, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 22 37 44 467 483 451 451 451), lower := (rows 11 22 37 44 16 32 64 128 256), losses := [] }

theorem u41164 : Upper (D 6) (R 6) [10,20,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41165 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41165 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41165 : Upper (D 6) (R 6) [10,20,33,65] 13 := by
  apply FastRouting.sound _ _ [10,20,33,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r41165 c41165
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30004
  · exact u30005
  · exact u30006
  · exact u30007
  · exact u30008
  · exact u30009
  · exact u30010
  · exact u30011
  · exact u30012
  · exact u30013
  · exact u30014

def b41166 : PairBound 9 := { available := 485, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 37 74 501 485 485 485 485), lower := (rows 11 22 37 74 16 32 64 128 256), losses := [] }

theorem u41166 : Upper (D 6) (R 6) [10,20,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41167 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41167 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41167 : Upper (D 6) (R 6) [10,20,33,68] 13 := by
  apply FastRouting.sound _ _ [10,20,33,68] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,384] r41167 c41167
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30015
  · exact u30016
  · exact u30017
  · exact u30018
  · exact u30019
  · exact u30020
  · exact u30021
  · exact u30022
  · exact u30023
  · exact u30024
  · exact u30025

def r41168 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41168 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41168 : Upper (D 6) (R 6) [10,20,33,96] 13 := by
  apply FastRouting.sound _ _ [10,20,33,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41168 c41168
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30026
  · exact u30027
  · exact u30028
  · exact u30029
  · exact u30030
  · exact u30031
  · exact u30032
  · exact u30033
  · exact u30034
  · exact u30035
  · exact u30036

def r41169 : Route 9 := (fun mask => (mask,id))

def c41169 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41169 : Upper (D 6) (R 6) [10,20,33,129] 13 := by
  apply FastRouting.sound _ _ [10,20,33,129] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41169 c41169
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30037
  · exact u30038
  · exact u30039
  · exact u30040
  · exact u30041
  · exact u30042
  · exact u30043
  · exact u30044
  · exact u30045
  · exact u30046

def b41170 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 37 138 373 357 357 485 357), lower := (rows 11 22 37 138 16 32 64 128 256), losses := [] }

theorem u41170 : Upper (D 6) (R 6) [10,20,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41171 : Route 9 := (fun mask => (mask,id))

def c41171 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41171 : Upper (D 6) (R 6) [10,20,33,132] 13 := by
  apply FastRouting.sound _ _ [10,20,33,132] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41171 c41171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30047
  · exact u30048
  · exact u30049
  · exact u30050
  · exact u30051
  · exact u30052
  · exact u30053
  · exact u30054
  · exact u30055
  · exact u30056

def r41172 : Route 9 := (fun mask => (mask,id))

def c41172 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41172 : Upper (D 6) (R 6) [10,20,33,160] 13 := by
  apply FastRouting.sound _ _ [10,20,33,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41172 c41172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30057
  · exact u30058
  · exact u30059
  · exact u30060
  · exact u30061
  · exact u30062
  · exact u30063
  · exact u30064
  · exact u30065
  · exact u30066

def r41173 : Route 9 := (fun mask => (mask,id))

def c41173 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41173 : Upper (D 6) (R 6) [10,20,33,192] 13 := by
  apply FastRouting.sound _ _ [10,20,33,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41173 c41173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30067
  · exact u30068
  · exact u30069
  · exact u30070
  · exact u30071
  · exact u30072
  · exact u30073
  · exact u30074
  · exact u30075
  · exact u30076
  · exact u30077
  · exact u30078
  · exact u30079
  · exact u30080
  · exact u30081

def r41174 : Route 9 := (fun mask => (mask,id))

def c41174 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41174 : Upper (D 6) (R 6) [10,20,33,384] 13 := by
  apply FastRouting.sound _ _ [10,20,33,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41174 c41174
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30082
  · exact u30083
  · exact u30084
  · exact u30085
  · exact u30086
  · exact u30087
  · exact u30088
  · exact u30089
  · exact u30090
  · exact u30091

def b41175 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 38 13 497 481 481 481 481), lower := (rows 11 22 38 13 16 32 64 128 256), losses := [] }

theorem u41175 : Upper (D 6) (R 6) [10,20,34,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41176 : PairBound 9 := { available := 453, camps := [{ cop := 2, region := 9, targets := 4 },{ cop := 2, region := 9, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 38 41 469 485 453 453 453), lower := (rows 11 22 38 41 16 32 64 128 256), losses := [] }

theorem u41176 : Upper (D 6) (R 6) [10,20,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41177 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 38 44 465 481 449 449 449), lower := (rows 11 22 38 44 16 32 64 128 256), losses := [] }

theorem u41177 : Upper (D 6) (R 6) [10,20,34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41178 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41178 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41178 : Upper (D 6) (R 6) [10,20,34,65] 13 := by
  apply FastRouting.sound _ _ [10,20,34,65] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,384] r41178 c41178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30092
  · exact u30093
  · exact u30094
  · exact u30095
  · exact u30096
  · exact u30097
  · exact u30098
  · exact u30099
  · exact u30100
  · exact u30101
  · exact u30102

def r41179 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41179 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41179 : Upper (D 6) (R 6) [10,20,34,68] 13 := by
  apply FastRouting.sound _ _ [10,20,34,68] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r41179 c41179
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30103
  · exact u30104
  · exact u30105
  · exact u30106
  · exact u30107
  · exact u30108
  · exact u30109

def r41180 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41180 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41180 : Upper (D 6) (R 6) [10,20,34,96] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96] 13 (by decide) (choices 2) [5,65,68,129,132,192,384] r41180 c41180
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30110
  · exact u30111
  · exact u30112
  · exact u30113
  · exact u30114
  · exact u30115
  · exact u30116

def r41181 : Route 9 := (fun mask => (mask,id))

def c41181 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41181 : Upper (D 6) (R 6) [10,20,34,129] 13 := by
  apply FastRouting.sound _ _ [10,20,34,129] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41181 c41181
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30117
  · exact u30118
  · exact u30119
  · exact u30120
  · exact u30121
  · exact u30122
  · exact u30123
  · exact u30124
  · exact u30125
  · exact u30126

def r41182 : Route 9 := (fun mask => (mask,id))

def c41182 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41182 : Upper (D 6) (R 6) [10,20,34,132] 13 := by
  apply FastRouting.sound _ _ [10,20,34,132] 13 (by decide) (choices 2) [33,65,96,257,288,320] r41182 c41182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30127
  · exact u30128
  · exact u30129
  · exact u30130
  · exact u30131
  · exact u30132

def r41183 : Route 9 := (fun mask => (mask,id))

def c41183 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41183 : Upper (D 6) (R 6) [10,20,34,160] 13 := by
  apply FastRouting.sound _ _ [10,20,34,160] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41183 c41183
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30133
  · exact u30134
  · exact u30135
  · exact u30136
  · exact u30137
  · exact u30138

def r41184 : Route 9 := (fun mask => (mask,id))

def c41184 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41184 : Upper (D 6) (R 6) [10,20,34,192] 13 := by
  apply FastRouting.sound _ _ [10,20,34,192] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41184 c41184
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30139
  · exact u30140
  · exact u30141
  · exact u30142
  · exact u30143
  · exact u30144
  · exact u30145
  · exact u30146
  · exact u30147
  · exact u30148

def r41185 : Route 9 := (fun mask => (mask,id))

def c41185 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41185 : Upper (D 6) (R 6) [10,20,34,384] 13 := by
  apply FastRouting.sound _ _ [10,20,34,384] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41185 c41185
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30149
  · exact u30150
  · exact u30151
  · exact u30152
  · exact u30153
  · exact u30154

def b41186 : PairBound 9 := { available := 485, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 100 11 501 485 485 485 485), lower := (rows 11 22 100 11 16 32 64 128 256), losses := [] }

theorem u41186 : Upper (D 6) (R 6) [10,20,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41187 : PairBound 9 := { available := 483, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 100 13 499 483 483 483 483), lower := (rows 11 22 100 13 16 32 64 128 256), losses := [] }

theorem u41187 : Upper (D 6) (R 6) [10,20,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41188 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 100 14 497 481 481 481 481), lower := (rows 11 22 100 14 16 32 64 128 256), losses := [] }

theorem u41188 : Upper (D 6) (R 6) [10,20,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41189 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41189 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41189 : Upper (D 6) (R 6) [10,20,96,33] 13 := by
  apply FastRouting.sound _ _ [10,20,96,33] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41189 c41189
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30155
  · exact u30156
  · exact u30157
  · exact u30158
  · exact u30159
  · exact u30160
  · exact u30161
  · exact u30162
  · exact u30163
  · exact u30164
  · exact u30165

def b41190 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 100 42 469 485 453 453 453), lower := (rows 11 22 100 42 16 32 64 128 256), losses := [] }

theorem u41190 : Upper (D 6) (R 6) [10,20,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41191 : PairBound 9 := { available := 451, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 22 100 44 467 483 451 451 451), lower := (rows 11 22 100 44 16 32 64 128 256), losses := [] }

theorem u41191 : Upper (D 6) (R 6) [10,20,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41192 : PairBound 9 := { available := 391, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 22 100 104 407 423 455 391 391), lower := (rows 11 22 100 104 16 32 64 128 256), losses := [] }

theorem u41192 : Upper (D 6) (R 6) [10,20,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41193 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41193 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41193 : Upper (D 6) (R 6) [10,20,96,129] 13 := by
  apply FastRouting.sound _ _ [10,20,96,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r41193 c41193
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30166
  · exact u30167
  · exact u30168
  · exact u30169
  · exact u30170
  · exact u30171
  · exact u30172
  · exact u30173
  · exact u30174
  · exact u30175
  · exact u30176

def b41194 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 100 138 373 357 357 485 357), lower := (rows 11 22 100 138 16 32 64 128 256), losses := [] }

theorem u41194 : Upper (D 6) (R 6) [10,20,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41195 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41195 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41195 : Upper (D 6) (R 6) [10,20,96,132] 13 := by
  apply FastRouting.sound _ _ [10,20,96,132] 13 (by decide) (choices 2) [3,33,34,96,257,258,288] r41195 c41195
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30177
  · exact u30178
  · exact u30179
  · exact u30180
  · exact u30181
  · exact u30182
  · exact u30183

def r41196 : Route 9 := (fun mask => (mask,id))

def c41196 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41196 : Upper (D 6) (R 6) [10,20,96,160] 13 := by
  apply FastRouting.sound _ _ [10,20,96,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41196 c41196
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30184
  · exact u30185
  · exact u30186
  · exact u30187
  · exact u30188
  · exact u30189
  · exact u30190
  · exact u30191
  · exact u30192
  · exact u30193

def r41197 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41197 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41197 : Upper (D 6) (R 6) [10,20,96,384] 13 := by
  apply FastRouting.sound _ _ [10,20,96,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41197 c41197
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30194
  · exact u30195
  · exact u30196
  · exact u30197
  · exact u30198
  · exact u30199
  · exact u30200

def b41198 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 133 11 372 356 356 484 356), lower := (rows 11 22 133 11 16 32 64 128 256), losses := [] }

theorem u41198 : Upper (D 6) (R 6) [10,20,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41199 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 133 13 370 354 354 482 354), lower := (rows 11 22 133 13 16 32 64 128 256), losses := [] }

theorem u41199 : Upper (D 6) (R 6) [10,20,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41200 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 133 14 369 353 353 481 353), lower := (rows 11 22 133 14 16 32 64 128 256), losses := [] }

theorem u41200 : Upper (D 6) (R 6) [10,20,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41201 : Route 9 := (fun mask => (mask,id))

def c41201 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41201 : Upper (D 6) (R 6) [10,20,129,33] 13 := by
  apply FastRouting.sound _ _ [10,20,129,33] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41201 c41201
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30201
  · exact u30202
  · exact u30203
  · exact u30204
  · exact u30205
  · exact u30206
  · exact u30207
  · exact u30208
  · exact u30209
  · exact u30210

def b41202 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 133 42 373 357 357 485 357), lower := (rows 11 22 133 42 16 32 64 128 256), losses := [] }

theorem u41202 : Upper (D 6) (R 6) [10,20,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41203 : Route 9 := (fun mask => (mask,id))

def c41203 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41203 : Upper (D 6) (R 6) [10,20,129,36] 13 := by
  apply FastRouting.sound _ _ [10,20,129,36] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41203 c41203
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30211
  · exact u30212
  · exact u30213
  · exact u30214
  · exact u30215
  · exact u30216
  · exact u30217
  · exact u30218
  · exact u30219
  · exact u30220

def r41204 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41204 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41204 : Upper (D 6) (R 6) [10,20,129,96] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r41204 c41204
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30221
  · exact u30222
  · exact u30223
  · exact u30224
  · exact u30225
  · exact u30226
  · exact u30227
  · exact u30228
  · exact u30229
  · exact u30230
  · exact u30231

def r41205 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41205 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41205 : Upper (D 6) (R 6) [10,20,129,257] 13 := by
  apply FastRouting.sound _ _ [10,20,129,257] 13 (by decide) (choices 2) [6,34,36,96] r41205 c41205
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30232
  · exact u30233
  · exact u30234
  · exact u30235

def b41206 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 133 266 117 101 101 229 357), lower := (rows 11 22 133 266 16 32 64 128 256), losses := [] }

theorem u41206 : Upper (D 6) (R 6) [10,20,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41207 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41207 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41207 : Upper (D 6) (R 6) [10,20,129,260] 13 := by
  apply FastRouting.sound _ _ [10,20,129,260] 13 (by decide) (choices 2) [3,33,34,96] r41207 c41207
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30236
  · exact u30237
  · exact u30238
  · exact u30239

def r41208 : Route 9 := (fun mask => (mask,id))

def c41208 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41208 : Upper (D 6) (R 6) [10,20,129,288] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41208 c41208
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30240
  · exact u30241
  · exact u30242
  · exact u30243
  · exact u30244
  · exact u30245
  · exact u30246
  · exact u30247
  · exact u30248
  · exact u30249

def b41209 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 134 13 369 353 353 481 353), lower := (rows 11 22 134 13 16 32 64 128 256), losses := [] }

theorem u41209 : Upper (D 6) (R 6) [10,20,130,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41210 : Route 9 := (fun mask => (mask,id))

def c41210 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41210 : Upper (D 6) (R 6) [10,20,130,33] 13 := by
  apply FastRouting.sound _ _ [10,20,130,33] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41210 c41210
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30250
  · exact u30251
  · exact u30252
  · exact u30253
  · exact u30254
  · exact u30255
  · exact u30256
  · exact u30257
  · exact u30258
  · exact u30259

def r41211 : Route 9 := (fun mask => (mask,id))

def c41211 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41211 : Upper (D 6) (R 6) [10,20,130,36] 13 := by
  apply FastRouting.sound _ _ [10,20,130,36] 13 (by decide) (choices 2) [33,65,96,257,288,320] r41211 c41211
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30260
  · exact u30261
  · exact u30262
  · exact u30263
  · exact u30264
  · exact u30265

def r41212 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41212 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41212 : Upper (D 6) (R 6) [10,20,130,96] 13 := by
  apply FastRouting.sound _ _ [10,20,130,96] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r41212 c41212
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30266
  · exact u30267
  · exact u30268
  · exact u30269
  · exact u30270
  · exact u30271
  · exact u30272

def r41213 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41213 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41213 : Upper (D 6) (R 6) [10,20,130,257] 13 := by
  apply FastRouting.sound _ _ [10,20,130,257] 13 (by decide) (choices 2) [5,33,36,96] r41213 c41213
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30273
  · exact u30274
  · exact u30275
  · exact u30276

def r41214 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41214 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41214 : Upper (D 6) (R 6) [10,20,130,260] 13 := by
  apply FastRouting.sound _ _ [10,20,130,260] 13 (by decide) (choices 2) [33,96] r41214 c41214
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u30277
  · exact u30278

def r41215 : Route 9 := (fun mask => (mask,id))

def c41215 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41215 : Upper (D 6) (R 6) [10,20,130,288] 13 := by
  apply FastRouting.sound _ _ [10,20,130,288] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41215 c41215
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30279
  · exact u30280
  · exact u30281
  · exact u30282
  · exact u30283
  · exact u30284

def b41216 : PairBound 9 := { available := 357, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 22 164 11 373 357 357 485 357), lower := (rows 11 22 164 11 16 32 64 128 256), losses := [] }

theorem u41216 : Upper (D 6) (R 6) [10,20,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41217 : PairBound 9 := { available := 355, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 164 13 371 355 355 483 355), lower := (rows 11 22 164 13 16 32 64 128 256), losses := [] }

theorem u41217 : Upper (D 6) (R 6) [10,20,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41218 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 164 14 369 353 353 481 353), lower := (rows 11 22 164 14 16 32 64 128 256), losses := [] }

theorem u41218 : Upper (D 6) (R 6) [10,20,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41219 : Route 9 := (fun mask => (mask,id))

def c41219 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41219 : Upper (D 6) (R 6) [10,20,160,33] 13 := by
  apply FastRouting.sound _ _ [10,20,160,33] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41219 c41219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30285
  · exact u30286
  · exact u30287
  · exact u30288
  · exact u30289
  · exact u30290
  · exact u30291
  · exact u30292
  · exact u30293
  · exact u30294

#print axioms u41219
end Delivery.IrregularNine14.P06
