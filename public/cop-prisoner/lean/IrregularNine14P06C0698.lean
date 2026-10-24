import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0551
import IrregularNine14P06C0552
import IrregularNine14P06C0553
import IrregularNine14P06C0554
import IrregularNine14P06C0555
import IrregularNine14P06C0556

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41880 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 11 134 37 42 341 373 341 469 341), lower := (rows 11 134 37 42 16 32 64 128 256), losses := [] }

theorem u41880 : Upper (D 6) (R 6) [10,132,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41881 : PairBound 9 := { available := 339, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 134 37 44 339 371 339 467 339), lower := (rows 11 134 37 44 16 32 64 128 256), losses := [] }

theorem u41881 : Upper (D 6) (R 6) [10,132,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41882 : Route 9 := (fun mask => (mask,id))

def c41882 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41882 : Upper (D 6) (R 6) [10,132,33,48] 13 := by
  apply FastRouting.sound _ _ [10,132,33,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41882 c41882
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33061
  · exact u33062
  · exact u33063
  · exact u33064
  · exact u33065
  · exact u33066
  · exact u33067
  · exact u33068
  · exact u33069
  · exact u33070

def r41883 : Route 9 := (fun mask => (mask,id))

def c41883 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41883 : Upper (D 6) (R 6) [10,132,33,65] 13 := by
  apply FastRouting.sound _ _ [10,132,33,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41883 c41883
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33071
  · exact u33072
  · exact u33073
  · exact u33074
  · exact u33075
  · exact u33076
  · exact u33077
  · exact u33078
  · exact u33079
  · exact u33080

def b41884 : PairBound 9 := { available := 373, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 37 74 373 373 373 501 373), lower := (rows 11 134 37 74 16 32 64 128 256), losses := [] }

theorem u41884 : Upper (D 6) (R 6) [10,132,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41885 : Route 9 := (fun mask => (mask,id))

def c41885 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41885 : Upper (D 6) (R 6) [10,132,33,68] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41885 c41885
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33081
  · exact u33082
  · exact u33083
  · exact u33084
  · exact u33085
  · exact u33086
  · exact u33087
  · exact u33088
  · exact u33089
  · exact u33090

def r41886 : Route 9 := (fun mask => (mask,id))

def c41886 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41886 : Upper (D 6) (R 6) [10,132,33,80] 13 := by
  apply FastRouting.sound _ _ [10,132,33,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41886 c41886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33091
  · exact u33092
  · exact u33093
  · exact u33094
  · exact u33095
  · exact u33096
  · exact u33097
  · exact u33098
  · exact u33099
  · exact u33100
  · exact u33101
  · exact u33102
  · exact u33103
  · exact u33104
  · exact u33105

def r41887 : Route 9 := (fun mask => (mask,id))

def c41887 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41887 : Upper (D 6) (R 6) [10,132,33,96] 13 := by
  apply FastRouting.sound _ _ [10,132,33,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41887 c41887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33106
  · exact u33107
  · exact u33108
  · exact u33109
  · exact u33110
  · exact u33111
  · exact u33112
  · exact u33113
  · exact u33114
  · exact u33115

def r41888 : Route 9 := (fun mask => (mask,id))

def c41888 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41888 : Upper (D 6) (R 6) [10,132,33,257] 13 := by
  apply FastRouting.sound _ _ [10,132,33,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41888 c41888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33116
  · exact u33117
  · exact u33118
  · exact u33119
  · exact u33120
  · exact u33121

def b41889 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 37 266 117 117 117 245 373), lower := (rows 11 134 37 266 16 32 64 128 256), losses := [] }

theorem u41889 : Upper (D 6) (R 6) [10,132,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41890 : Route 9 := (fun mask => (mask,id))

def c41890 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41890 : Upper (D 6) (R 6) [10,132,33,260] 13 := by
  apply FastRouting.sound _ _ [10,132,33,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41890 c41890
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33122
  · exact u33123
  · exact u33124
  · exact u33125
  · exact u33126
  · exact u33127

def r41891 : Route 9 := (fun mask => (mask,id))

def c41891 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41891 : Upper (D 6) (R 6) [10,132,33,272] 13 := by
  apply FastRouting.sound _ _ [10,132,33,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41891 c41891
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33128
  · exact u33129
  · exact u33130
  · exact u33131
  · exact u33132
  · exact u33133
  · exact u33134
  · exact u33135
  · exact u33136
  · exact u33137

def r41892 : Route 9 := (fun mask => (mask,id))

def c41892 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41892 : Upper (D 6) (R 6) [10,132,33,288] 13 := by
  apply FastRouting.sound _ _ [10,132,33,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41892 c41892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33138
  · exact u33139
  · exact u33140
  · exact u33141
  · exact u33142
  · exact u33143

def r41893 : Route 9 := (fun mask => (mask,id))

def c41893 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41893 : Upper (D 6) (R 6) [10,132,33,320] 13 := by
  apply FastRouting.sound _ _ [10,132,33,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41893 c41893
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33144
  · exact u33145
  · exact u33146
  · exact u33147
  · exact u33148
  · exact u33149
  · exact u33150
  · exact u33151
  · exact u33152
  · exact u33153

def b41894 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 38 13 369 369 369 497 369), lower := (rows 11 134 38 13 16 32 64 128 256), losses := [] }

theorem u41894 : Upper (D 6) (R 6) [10,132,34,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41895 : Route 9 := (fun mask => (mask,id))

def c41895 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41895 : Upper (D 6) (R 6) [10,132,34,17] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41895 c41895
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33154
  · exact u33155
  · exact u33156
  · exact u33157
  · exact u33158
  · exact u33159
  · exact u33160
  · exact u33161
  · exact u33162
  · exact u33163

def r41896 : Route 9 := (fun mask => (mask,id))

def c41896 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41896 : Upper (D 6) (R 6) [10,132,34,20] 13 := by
  apply FastRouting.sound _ _ [10,132,34,20] 13 (by decide) (choices 2) [33,65,96,257,288,320] r41896 c41896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33164
  · exact u33165
  · exact u33166
  · exact u33167
  · exact u33168
  · exact u33169

def b41897 : PairBound 9 := { available := 341, camps := [{ cop := 2, region := 9, targets := 4 },{ cop := 2, region := 9, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 38 41 341 373 341 469 341), lower := (rows 11 134 38 41 16 32 64 128 256), losses := [] }

theorem u41897 : Upper (D 6) (R 6) [10,132,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41898 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 134 38 44 337 369 337 465 337), lower := (rows 11 134 38 44 16 32 64 128 256), losses := [] }

theorem u41898 : Upper (D 6) (R 6) [10,132,34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41899 : Route 9 := (fun mask => (mask,id))

def c41899 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41899 : Upper (D 6) (R 6) [10,132,34,48] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41899 c41899
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33170
  · exact u33171
  · exact u33172
  · exact u33173
  · exact u33174
  · exact u33175

def r41900 : Route 9 := (fun mask => (mask,id))

def c41900 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41900 : Upper (D 6) (R 6) [10,132,34,65] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41900 c41900
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33176
  · exact u33177
  · exact u33178
  · exact u33179
  · exact u33180
  · exact u33181
  · exact u33182
  · exact u33183
  · exact u33184
  · exact u33185

def r41901 : Route 9 := (fun mask => (mask,id))

def c41901 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41901 : Upper (D 6) (R 6) [10,132,34,68] 13 := by
  apply FastRouting.sound _ _ [10,132,34,68] 13 (by decide) (choices 2) [33,65,96,257,288,320] r41901 c41901
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33186
  · exact u33187
  · exact u33188
  · exact u33189
  · exact u33190
  · exact u33191

def r41902 : Route 9 := (fun mask => (mask,id))

def c41902 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41902 : Upper (D 6) (R 6) [10,132,34,80] 13 := by
  apply FastRouting.sound _ _ [10,132,34,80] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41902 c41902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33192
  · exact u33193
  · exact u33194
  · exact u33195
  · exact u33196
  · exact u33197
  · exact u33198
  · exact u33199
  · exact u33200
  · exact u33201

def r41903 : Route 9 := (fun mask => (mask,id))

def c41903 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41903 : Upper (D 6) (R 6) [10,132,34,96] 13 := by
  apply FastRouting.sound _ _ [10,132,34,96] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41903 c41903
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33202
  · exact u33203
  · exact u33204
  · exact u33205
  · exact u33206
  · exact u33207

def r41904 : Route 9 := (fun mask => (mask,id))

def c41904 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41904 : Upper (D 6) (R 6) [10,132,34,257] 13 := by
  apply FastRouting.sound _ _ [10,132,34,257] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41904 c41904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33208
  · exact u33209
  · exact u33210
  · exact u33211
  · exact u33212
  · exact u33213

def r41905 : Route 9 := (fun mask => (mask,id))

def c41905 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41905 : Upper (D 6) (R 6) [10,132,34,260] 13 := by
  apply FastRouting.sound _ _ [10,132,34,260] 13 (by decide) (choices 2) [33,65,96] r41905 c41905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33214
  · exact u33215
  · exact u33216

def r41906 : Route 9 := (fun mask => (mask,id))

def c41906 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41906 : Upper (D 6) (R 6) [10,132,34,272] 13 := by
  apply FastRouting.sound _ _ [10,132,34,272] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41906 c41906
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33217
  · exact u33218
  · exact u33219
  · exact u33220
  · exact u33221
  · exact u33222

def r41907 : Route 9 := (fun mask => (mask,id))

def c41907 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41907 : Upper (D 6) (R 6) [10,132,34,288] 13 := by
  apply FastRouting.sound _ _ [10,132,34,288] 13 (by decide) (choices 2) [5,65,68] r41907 c41907
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33223
  · exact u33224
  · exact u33225

def r41908 : Route 9 := (fun mask => (mask,id))

def c41908 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41908 : Upper (D 6) (R 6) [10,132,34,320] 13 := by
  apply FastRouting.sound _ _ [10,132,34,320] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41908 c41908
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33226
  · exact u33227
  · exact u33228
  · exact u33229
  · exact u33230
  · exact u33231

def b41909 : PairBound 9 := { available := 357, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 52 11 373 357 357 485 357), lower := (rows 11 134 52 11 16 32 64 128 256), losses := [] }

theorem u41909 : Upper (D 6) (R 6) [10,132,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41910 : PairBound 9 := { available := 355, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 52 13 371 355 355 483 355), lower := (rows 11 134 52 13 16 32 64 128 256), losses := [] }

theorem u41910 : Upper (D 6) (R 6) [10,132,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41911 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 52 14 369 353 353 481 353), lower := (rows 11 134 52 14 16 32 64 128 256), losses := [] }

theorem u41911 : Upper (D 6) (R 6) [10,132,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41912 : Route 9 := (fun mask => (mask,id))

def c41912 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41912 : Upper (D 6) (R 6) [10,132,48,33] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41912 c41912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33232
  · exact u33233
  · exact u33234
  · exact u33235
  · exact u33236
  · exact u33237
  · exact u33238
  · exact u33239
  · exact u33240
  · exact u33241

def b41913 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 52 42 341 357 325 453 325), lower := (rows 11 134 52 42 16 32 64 128 256), losses := [] }

theorem u41913 : Upper (D 6) (R 6) [10,132,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41914 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 134 52 44 339 355 323 451 323), lower := (rows 11 134 52 44 16 32 64 128 256), losses := [] }

theorem u41914 : Upper (D 6) (R 6) [10,132,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41915 : Route 9 := (fun mask => (mask,id))

def c41915 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41915 : Upper (D 6) (R 6) [10,132,48,65] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41915 c41915
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33242
  · exact u33243
  · exact u33244
  · exact u33245
  · exact u33246
  · exact u33247
  · exact u33248
  · exact u33249
  · exact u33250
  · exact u33251
  · exact u33252
  · exact u33253
  · exact u33254
  · exact u33255
  · exact u33256

def b41916 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 52 74 373 357 357 485 357), lower := (rows 11 134 52 74 16 32 64 128 256), losses := [] }

theorem u41916 : Upper (D 6) (R 6) [10,132,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41917 : Route 9 := (fun mask => (mask,id))

def c41917 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41917 : Upper (D 6) (R 6) [10,132,48,68] 13 := by
  apply FastRouting.sound _ _ [10,132,48,68] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41917 c41917
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33257
  · exact u33258
  · exact u33259
  · exact u33260
  · exact u33261
  · exact u33262
  · exact u33263
  · exact u33264
  · exact u33265
  · exact u33266

def r41918 : Route 9 := (fun mask => (mask,id))

def c41918 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41918 : Upper (D 6) (R 6) [10,132,48,96] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41918 c41918
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33267
  · exact u33268
  · exact u33269
  · exact u33270
  · exact u33271
  · exact u33272
  · exact u33273
  · exact u33274
  · exact u33275
  · exact u33276

def r41919 : Route 9 := (fun mask => (mask,id))

def c41919 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41919 : Upper (D 6) (R 6) [10,132,48,257] 13 := by
  apply FastRouting.sound _ _ [10,132,48,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41919 c41919
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33277
  · exact u33278
  · exact u33279
  · exact u33280
  · exact u33281
  · exact u33282
  · exact u33283
  · exact u33284
  · exact u33285
  · exact u33286

def b41920 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 52 266 117 101 101 229 357), lower := (rows 11 134 52 266 16 32 64 128 256), losses := [] }

theorem u41920 : Upper (D 6) (R 6) [10,132,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41921 : Route 9 := (fun mask => (mask,id))

def c41921 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41921 : Upper (D 6) (R 6) [10,132,48,260] 13 := by
  apply FastRouting.sound _ _ [10,132,48,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41921 c41921
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33287
  · exact u33288
  · exact u33289
  · exact u33290
  · exact u33291
  · exact u33292

def r41922 : Route 9 := (fun mask => (mask,id))

def c41922 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41922 : Upper (D 6) (R 6) [10,132,48,288] 13 := by
  apply FastRouting.sound _ _ [10,132,48,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41922 c41922
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33293
  · exact u33294
  · exact u33295
  · exact u33296
  · exact u33297
  · exact u33298

def r41923 : Route 9 := (fun mask => (mask,id))

def c41923 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41923 : Upper (D 6) (R 6) [10,132,48,320] 13 := by
  apply FastRouting.sound _ _ [10,132,48,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41923 c41923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33299
  · exact u33300
  · exact u33301
  · exact u33302
  · exact u33303
  · exact u33304
  · exact u33305
  · exact u33306
  · exact u33307
  · exact u33308

def b41924 : PairBound 9 := { available := 373, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 100 11 373 373 373 501 373), lower := (rows 11 134 100 11 16 32 64 128 256), losses := [] }

theorem u41924 : Upper (D 6) (R 6) [10,132,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41925 : PairBound 9 := { available := 371, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 100 13 371 371 371 499 371), lower := (rows 11 134 100 13 16 32 64 128 256), losses := [] }

theorem u41925 : Upper (D 6) (R 6) [10,132,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41926 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 100 14 369 369 369 497 369), lower := (rows 11 134 100 14 16 32 64 128 256), losses := [] }

theorem u41926 : Upper (D 6) (R 6) [10,132,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41927 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41927 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41927 : Upper (D 6) (R 6) [10,132,96,17] 13 := by
  apply FastRouting.sound _ _ [10,132,96,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r41927 c41927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33309
  · exact u33310
  · exact u33311
  · exact u33312
  · exact u33313
  · exact u33314
  · exact u33315
  · exact u33316
  · exact u33317
  · exact u33318
  · exact u33319

def b41928 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 100 26 373 357 357 485 357), lower := (rows 11 134 100 26 16 32 64 128 256), losses := [] }

theorem u41928 : Upper (D 6) (R 6) [10,132,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41929 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41929 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41929 : Upper (D 6) (R 6) [10,132,96,20] 13 := by
  apply FastRouting.sound _ _ [10,132,96,20] 13 (by decide) (choices 2) [3,33,34,96,257,258,288] r41929 c41929
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33320
  · exact u33321
  · exact u33322
  · exact u33323
  · exact u33324
  · exact u33325
  · exact u33326

def r41930 : Route 9 := (fun mask => (mask,id))

def c41930 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41930 : Upper (D 6) (R 6) [10,132,96,33] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41930 c41930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33327
  · exact u33328
  · exact u33329
  · exact u33330
  · exact u33331
  · exact u33332
  · exact u33333
  · exact u33334
  · exact u33335
  · exact u33336

def b41931 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 100 42 341 373 341 469 341), lower := (rows 11 134 100 42 16 32 64 128 256), losses := [] }

theorem u41931 : Upper (D 6) (R 6) [10,132,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41932 : PairBound 9 := { available := 339, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 134 100 44 339 371 339 467 339), lower := (rows 11 134 100 44 16 32 64 128 256), losses := [] }

theorem u41932 : Upper (D 6) (R 6) [10,132,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41933 : Route 9 := (fun mask => (mask,id))

def c41933 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41933 : Upper (D 6) (R 6) [10,132,96,48] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41933 c41933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33337
  · exact u33338
  · exact u33339
  · exact u33340
  · exact u33341
  · exact u33342
  · exact u33343
  · exact u33344
  · exact u33345
  · exact u33346

def b41934 : PairBound 9 := { available := 279, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 134 100 104 279 311 343 407 279), lower := (rows 11 134 100 104 16 32 64 128 256), losses := [] }

theorem u41934 : Upper (D 6) (R 6) [10,132,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41935 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41935 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41935 : Upper (D 6) (R 6) [10,132,96,257] 13 := by
  apply FastRouting.sound _ _ [10,132,96,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41935 c41935
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33347
  · exact u33348
  · exact u33349
  · exact u33350
  · exact u33351
  · exact u33352
  · exact u33353

def b41936 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 100 266 117 117 117 245 373), lower := (rows 11 134 100 266 16 32 64 128 256), losses := [] }

theorem u41936 : Upper (D 6) (R 6) [10,132,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41937 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41937 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41937 : Upper (D 6) (R 6) [10,132,96,260] 13 := by
  apply FastRouting.sound _ _ [10,132,96,260] 13 (by decide) (choices 2) [3,33,34,96] r41937 c41937
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33354
  · exact u33355
  · exact u33356
  · exact u33357

def r41938 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41938 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41938 : Upper (D 6) (R 6) [10,132,96,272] 13 := by
  apply FastRouting.sound _ _ [10,132,96,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41938 c41938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33358
  · exact u33359
  · exact u33360
  · exact u33361
  · exact u33362
  · exact u33363
  · exact u33364

def r41939 : Route 9 := (fun mask => (mask,id))

def c41939 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41939 : Upper (D 6) (R 6) [10,132,96,288] 13 := by
  apply FastRouting.sound _ _ [10,132,96,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41939 c41939
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33365
  · exact u33366
  · exact u33367
  · exact u33368
  · exact u33369
  · exact u33370

#print axioms u41939
end Delivery.IrregularNine14.P06
