import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0550
import IrregularNine14P07C0551
import IrregularNine14P07C0552
import IrregularNine14P07C0553
import IrregularNine14P07C0554

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41760 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41760 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41760 : Upper (D 7) (R 7) [12,96,17,258] 13 := by
  apply FastRouting.sound _ _ [12,96,17,258] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41760 c41760
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33048
  · exact u33049
  · exact u33050
  · exact u33051
  · exact u33052
  · exact u33053
  · exact u33054

def r41761 : Route 9 := (fun mask => (mask,id))

def c41761 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41761 : Upper (D 7) (R 7) [12,96,17,288] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41761 c41761
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33055
  · exact u33056
  · exact u33057
  · exact u33058
  · exact u33059
  · exact u33060

def r41762 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41762 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41762 : Upper (D 7) (R 7) [12,96,17,384] 13 := by
  apply FastRouting.sound _ _ [12,96,17,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41762 c41762
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33061
  · exact u33062
  · exact u33063
  · exact u33064
  · exact u33065
  · exact u33066
  · exact u33067

def r41763 : Route 9 := (fun mask => (mask,id))

def c41763 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41763 : Upper (D 7) (R 7) [12,96,18,33] 13 := by
  apply FastRouting.sound _ _ [12,96,18,33] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41763 c41763
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33068
  · exact u33069
  · exact u33070
  · exact u33071
  · exact u33072
  · exact u33073
  · exact u33074
  · exact u33075
  · exact u33076
  · exact u33077

def b41764 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 13 98 22 42 465 481 449 449 449), lower := (rows 13 98 22 42 16 32 64 128 256), losses := [] }

theorem u41764 : Upper (D 7) (R 7) [12,96,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41765 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 13 98 22 104 403 419 451 387 387), lower := (rows 13 98 22 104 16 32 64 128 256), losses := [] }

theorem u41765 : Upper (D 7) (R 7) [12,96,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41766 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41766 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41766 : Upper (D 7) (R 7) [12,96,18,129] 13 := by
  apply FastRouting.sound _ _ [12,96,18,129] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r41766 c41766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33078
  · exact u33079
  · exact u33080
  · exact u33081
  · exact u33082
  · exact u33083
  · exact u33084
  · exact u33085
  · exact u33086
  · exact u33087
  · exact u33088

def r41767 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41767 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41767 : Upper (D 7) (R 7) [12,96,18,130] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r41767 c41767
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33089
  · exact u33090
  · exact u33091
  · exact u33092
  · exact u33093
  · exact u33094
  · exact u33095

def r41768 : Route 9 := (fun mask => (mask,id))

def c41768 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41768 : Upper (D 7) (R 7) [12,96,18,160] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41768 c41768
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def r41769 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41769 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41769 : Upper (D 7) (R 7) [12,96,18,257] 13 := by
  apply FastRouting.sound _ _ [12,96,18,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41769 c41769
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33106
  · exact u33107
  · exact u33108
  · exact u33109
  · exact u33110
  · exact u33111
  · exact u33112

def r41770 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41770 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41770 : Upper (D 7) (R 7) [12,96,18,258] 13 := by
  apply FastRouting.sound _ _ [12,96,18,258] 13 (by decide) (choices 2) [33,96,129,160] r41770 c41770
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33113
  · exact u33114
  · exact u33115
  · exact u33116

def r41771 : Route 9 := (fun mask => (mask,id))

def c41771 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41771 : Upper (D 7) (R 7) [12,96,18,288] 13 := by
  apply FastRouting.sound _ _ [12,96,18,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41771 c41771
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33117
  · exact u33118
  · exact u33119
  · exact u33120
  · exact u33121
  · exact u33122

def r41772 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41772 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41772 : Upper (D 7) (R 7) [12,96,18,384] 13 := by
  apply FastRouting.sound _ _ [12,96,18,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41772 c41772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33123
  · exact u33124
  · exact u33125
  · exact u33126
  · exact u33127
  · exact u33128
  · exact u33129

def b41773 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 13, targets := 2 },{ cop := 1, region := 13, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 13 98 37 73 402 434 466 402 402), lower := (rows 13 98 37 73 16 32 64 128 256), losses := [] }

theorem u41773 : Upper (D 7) (R 7) [12,96,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41774 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 13, targets := 128 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 13 98 37 74 403 435 467 403 403), lower := (rows 13 98 37 74 16 32 64 128 256), losses := [] }

theorem u41774 : Upper (D 7) (R 7) [12,96,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41775 : Route 9 := (fun mask => (mask,id))

def c41775 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41775 : Upper (D 7) (R 7) [12,96,33,80] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80] 13 (by decide) (choices 2) [3,129,130,257,258,384] r41775 c41775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33130
  · exact u33131
  · exact u33132
  · exact u33133
  · exact u33134
  · exact u33135

def r41776 : Route 9 := (fun mask => (mask,id))

def c41776 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41776 : Upper (D 7) (R 7) [12,96,33,129] 13 := by
  apply FastRouting.sound _ _ [12,96,33,129] 13 (by decide) (choices 2) [66,130,192,258,320,384] r41776 c41776
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33136
  · exact u33137
  · exact u33138
  · exact u33139
  · exact u33140
  · exact u33141

def r41777 : Route 9 := (fun mask => (mask,id))

def c41777 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41777 : Upper (D 7) (R 7) [12,96,33,130] 13 := by
  apply FastRouting.sound _ _ [12,96,33,130] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41777 c41777
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33142
  · exact u33143
  · exact u33144
  · exact u33145
  · exact u33146
  · exact u33147
  · exact u33148
  · exact u33149
  · exact u33150
  · exact u33151

def r41778 : Route 9 := (fun mask => (mask,id))

def c41778 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41778 : Upper (D 7) (R 7) [12,96,33,144] 13 := by
  apply FastRouting.sound _ _ [12,96,33,144] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41778 c41778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33152
  · exact u33153
  · exact u33154
  · exact u33155
  · exact u33156
  · exact u33157
  · exact u33158
  · exact u33159
  · exact u33160
  · exact u33161

def r41779 : Route 9 := (fun mask => (mask,id))

def c41779 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41779 : Upper (D 7) (R 7) [12,96,33,192] 13 := by
  apply FastRouting.sound _ _ [12,96,33,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r41779 c41779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33162
  · exact u33163
  · exact u33164
  · exact u33165
  · exact u33166
  · exact u33167

def r41780 : Route 9 := (fun mask => (mask,id))

def c41780 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41780 : Upper (D 7) (R 7) [12,96,33,257] 13 := by
  apply FastRouting.sound _ _ [12,96,33,257] 13 (by decide) (choices 2) [66,130,192] r41780 c41780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33168
  · exact u33169
  · exact u33170

def r41781 : Route 9 := (fun mask => (mask,id))

def c41781 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41781 : Upper (D 7) (R 7) [12,96,33,258] 13 := by
  apply FastRouting.sound _ _ [12,96,33,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41781 c41781
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33171
  · exact u33172
  · exact u33173
  · exact u33174
  · exact u33175
  · exact u33176

def r41782 : Route 9 := (fun mask => (mask,id))

def c41782 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41782 : Upper (D 7) (R 7) [12,96,33,272] 13 := by
  apply FastRouting.sound _ _ [12,96,33,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41782 c41782
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33177
  · exact u33178
  · exact u33179
  · exact u33180
  · exact u33181
  · exact u33182

def r41783 : Route 9 := (fun mask => (mask,id))

def c41783 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41783 : Upper (D 7) (R 7) [12,96,33,320] 13 := by
  apply FastRouting.sound _ _ [12,96,33,320] 13 (by decide) (choices 2) [3,129,130] r41783 c41783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33183
  · exact u33184
  · exact u33185

def r41784 : Route 9 := (fun mask => (mask,id))

def c41784 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41784 : Upper (D 7) (R 7) [12,96,33,384] 13 := by
  apply FastRouting.sound _ _ [12,96,33,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41784 c41784
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

def b41785 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 88 403 419 451 387 387), lower := (rows 13 98 38 88 16 32 64 128 256), losses := [] }

theorem u41785 : Upper (D 7) (R 7) [12,96,34,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41786 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 137 467 499 467 467 467), lower := (rows 13 98 38 137 16 32 64 128 256), losses := [] }

theorem u41786 : Upper (D 7) (R 7) [12,96,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41787 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 138 465 497 465 465 465), lower := (rows 13 98 38 138 16 32 64 128 256), losses := [] }

theorem u41787 : Upper (D 7) (R 7) [12,96,34,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41788 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 152 467 483 451 451 451), lower := (rows 13 98 38 152 16 32 64 128 256), losses := [] }

theorem u41788 : Upper (D 7) (R 7) [12,96,34,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41789 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 200 403 435 467 403 403), lower := (rows 13 98 38 200 16 32 64 128 256), losses := [] }

theorem u41789 : Upper (D 7) (R 7) [12,96,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41790 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 265 211 243 211 211 467), lower := (rows 13 98 38 265 16 32 64 128 256), losses := [] }

theorem u41790 : Upper (D 7) (R 7) [12,96,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41791 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 266 209 241 209 209 465), lower := (rows 13 98 38 266 16 32 64 128 256), losses := [] }

theorem u41791 : Upper (D 7) (R 7) [12,96,34,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41792 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 280 211 227 195 195 451), lower := (rows 13 98 38 280 16 32 64 128 256), losses := [] }

theorem u41792 : Upper (D 7) (R 7) [12,96,34,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41793 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 328 147 179 211 147 403), lower := (rows 13 98 38 328 16 32 64 128 256), losses := [] }

theorem u41793 : Upper (D 7) (R 7) [12,96,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41794 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 98 38 392 211 243 211 211 467), lower := (rows 13 98 38 392 16 32 64 128 256), losses := [] }

theorem u41794 : Upper (D 7) (R 7) [12,96,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41795 : Route 9 := (fun mask => (mask,id))

def c41795 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41795 : Upper (D 7) (R 7) [12,96,48,129] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41795 c41795
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

def r41796 : Route 9 := (fun mask => (mask,id))

def c41796 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41796 : Upper (D 7) (R 7) [12,96,48,130] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41796 c41796
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33202
  · exact u33203
  · exact u33204
  · exact u33205
  · exact u33206
  · exact u33207
  · exact u33208
  · exact u33209
  · exact u33210
  · exact u33211

def r41797 : Route 9 := (fun mask => (mask,id))

def c41797 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41797 : Upper (D 7) (R 7) [12,96,48,192] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r41797 c41797
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33212
  · exact u33213
  · exact u33214
  · exact u33215
  · exact u33216
  · exact u33217

def r41798 : Route 9 := (fun mask => (mask,id))

def c41798 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41798 : Upper (D 7) (R 7) [12,96,48,257] 13 := by
  apply FastRouting.sound _ _ [12,96,48,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41798 c41798
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33218
  · exact u33219
  · exact u33220
  · exact u33221
  · exact u33222
  · exact u33223

def r41799 : Route 9 := (fun mask => (mask,id))

def c41799 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41799 : Upper (D 7) (R 7) [12,96,48,258] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41799 c41799
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33224
  · exact u33225
  · exact u33226
  · exact u33227
  · exact u33228
  · exact u33229

def r41800 : Route 9 := (fun mask => (mask,id))

def c41800 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41800 : Upper (D 7) (R 7) [12,96,48,320] 13 := by
  apply FastRouting.sound _ _ [12,96,48,320] 13 (by decide) (choices 2) [3,129,130] r41800 c41800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33230
  · exact u33231
  · exact u33232

def r41801 : Route 9 := (fun mask => (mask,id))

def c41801 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41801 : Upper (D 7) (R 7) [12,96,48,384] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41801 c41801
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33233
  · exact u33234
  · exact u33235
  · exact u33236
  · exact u33237
  · exact u33238

def b41802 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 4, targets := 129 },{ cop := 2, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 100 137 403 435 467 403 403), lower := (rows 13 98 100 137 16 32 64 128 256), losses := [] }

theorem u41802 : Upper (D 7) (R 7) [12,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41803 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 4, targets := 129 },{ cop := 2, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 100 138 403 435 467 403 403), lower := (rows 13 98 100 138 16 32 64 128 256), losses := [] }

theorem u41803 : Upper (D 7) (R 7) [12,96,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41804 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 4, targets := 129 },{ cop := 2, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 100 152 403 419 451 387 387), lower := (rows 13 98 100 152 16 32 64 128 256), losses := [] }

theorem u41804 : Upper (D 7) (R 7) [12,96,96,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41805 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 4, targets := 129 },{ cop := 2, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 100 265 147 179 211 147 403), lower := (rows 13 98 100 265 16 32 64 128 256), losses := [] }

theorem u41805 : Upper (D 7) (R 7) [12,96,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41806 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 4, targets := 129 },{ cop := 2, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 100 266 147 179 211 147 403), lower := (rows 13 98 100 266 16 32 64 128 256), losses := [] }

theorem u41806 : Upper (D 7) (R 7) [12,96,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41807 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 4, targets := 129 },{ cop := 2, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 100 280 147 163 195 131 387), lower := (rows 13 98 100 280 16 32 64 128 256), losses := [] }

theorem u41807 : Upper (D 7) (R 7) [12,96,96,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41808 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 4, targets := 129 },{ cop := 2, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 100 392 147 179 211 147 403), lower := (rows 13 98 100 392 16 32 64 128 256), losses := [] }

theorem u41808 : Upper (D 7) (R 7) [12,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41809 : PairBound 9 := { available := 370, camps := [{ cop := 7, region := 13, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 133 137 370 370 370 498 370), lower := (rows 13 98 133 137 16 32 64 128 256), losses := [] }

theorem u41809 : Upper (D 7) (R 7) [12,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41810 : PairBound 9 := { available := 371, camps := [{ cop := 3, region := 5, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 133 138 371 371 371 499 371), lower := (rows 13 98 133 138 16 32 64 128 256), losses := [] }

theorem u41810 : Upper (D 7) (R 7) [12,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41811 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 5, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 133 152 371 355 355 483 355), lower := (rows 13 98 133 152 16 32 64 128 256), losses := [] }

theorem u41811 : Upper (D 7) (R 7) [12,96,129,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41812 : PairBound 9 := { available := 339, camps := [{ cop := 3, region := 5, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 133 168 339 371 339 467 339), lower := (rows 13 98 133 168 16 32 64 128 256), losses := [] }

theorem u41812 : Upper (D 7) (R 7) [12,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41813 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41813 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41813 : Upper (D 7) (R 7) [12,96,129,257] 13 := by
  apply FastRouting.sound _ _ [12,96,129,257] 13 (by decide) (choices 2) [34,96,130,160] r41813 c41813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33239
  · exact u33240
  · exact u33241
  · exact u33242

def r41814 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41814 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41814 : Upper (D 7) (R 7) [12,96,129,258] 13 := by
  apply FastRouting.sound _ _ [12,96,129,258] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41814 c41814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33243
  · exact u33244
  · exact u33245
  · exact u33246
  · exact u33247
  · exact u33248
  · exact u33249

def r41815 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41815 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41815 : Upper (D 7) (R 7) [12,96,129,272] 13 := by
  apply FastRouting.sound _ _ [12,96,129,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41815 c41815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33250
  · exact u33251
  · exact u33252
  · exact u33253
  · exact u33254
  · exact u33255
  · exact u33256

def r41816 : Route 9 := (fun mask => (mask,id))

def c41816 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41816 : Upper (D 7) (R 7) [12,96,129,288] 13 := by
  apply FastRouting.sound _ _ [12,96,129,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41816 c41816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33257
  · exact u33258
  · exact u33259
  · exact u33260
  · exact u33261
  · exact u33262

def b41817 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 5, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 133 392 115 115 115 243 371), lower := (rows 13 98 133 392 16 32 64 128 256), losses := [] }

theorem u41817 : Upper (D 7) (R 7) [12,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41818 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5),(3,6)], upper := (rows 13 98 134 138 369 369 369 497 369), lower := (rows 13 98 134 138 16 32 64 128 256), losses := [] }

theorem u41818 : Upper (D 7) (R 7) [12,96,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41819 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41819 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41819 : Upper (D 7) (R 7) [12,96,130,144] 13 := by
  apply FastRouting.sound _ _ [12,96,130,144] 13 (by decide) (choices 2) [3,33,34,96,257,258,288] r41819 c41819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33263
  · exact u33264
  · exact u33265
  · exact u33266
  · exact u33267
  · exact u33268
  · exact u33269

#print axioms u41819
end Delivery.IrregularNine14.P07
