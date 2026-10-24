import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0318
import IrregularNine14P08C0319
import IrregularNine14P08C0320
import IrregularNine14P08C0321
import IrregularNine14P08C0322
import IrregularNine14P08C0323
import IrregularNine14P08C0324

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r23880 : Route 9 := (fun mask => (mask,id))

def c23880 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23880 : Upper (D 8) (R 8) [6,72,288] 13 := by
  apply FastRouting.sound _ _ [6,72,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23880 c23880
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19097
  · exact u19098
  · exact u19099
  · exact u19100
  · exact u19101
  · exact u19102
  · exact u19103
  · exact u19104
  · exact u19105
  · exact u19106

def b23881 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 324 185 177 177 241 177 433), lower := (rows 7 74 324 8 16 32 64 128 256), losses := [] }

theorem u23881 : Upper (D 8) (R 8) [6,72,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23882 : Route 9 := (fun mask => (mask,id))

def c23882 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23882 : Upper (D 8) (R 8) [6,72,384] 13 := by
  apply FastRouting.sound _ _ [6,72,384] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23882 c23882
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19107
  · exact u19108
  · exact u19109
  · exact u19110
  · exact u19111
  · exact u19112
  · exact u19113
  · exact u19114
  · exact u19115
  · exact u19116

def b23883 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 100 441 441 441 505 441 441), lower := (rows 7 98 100 8 16 32 64 128 256), losses := [] }

theorem u23883 : Upper (D 8) (R 8) [6,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23884_129 : Upper (D 8) (R 8) [6,96,160,129] 13 :=
  permutation_upper _ _ _ [6,96,160,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19120

theorem m23884_144 : Upper (D 8) (R 8) [6,96,160,144] 13 :=
  permutation_upper _ _ _ [6,96,160,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19121

theorem m23884_160 : Upper (D 8) (R 8) [6,96,160,160] 13 :=
  permutation_upper _ _ _ [6,96,160,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19122

theorem m23884_384 : Upper (D 8) (R 8) [6,96,160,384] 13 :=
  permutation_upper _ _ _ [6,96,160,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19127

def r23884 : Route 9 := (fun mask => (mask,id))

def c23884 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23884 : Upper (D 8) (R 8) [6,96,160] 13 := by
  apply FastRouting.sound _ _ [6,96,160] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23884 c23884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19117
  · exact u19118
  · exact u19119
  · exact u19120
  · exact u19121
  · exact u19122
  · exact m23884_129
  · exact m23884_144
  · exact m23884_160
  · exact u19123
  · exact u19124
  · exact u19125
  · exact u19126
  · exact u19127
  · exact m23884_384

def b23885 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 196 441 441 441 505 441 441), lower := (rows 7 98 196 8 16 32 64 128 256), losses := [] }

theorem u23885 : Upper (D 8) (R 8) [6,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23886 : Route 9 := (fun mask => (mask,id))

def c23886 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23886 : Upper (D 8) (R 8) [6,96,257] 13 := by
  apply FastRouting.sound _ _ [6,96,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23886 c23886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19128
  · exact u19129
  · exact u19130
  · exact u19131
  · exact u19132
  · exact u19133
  · exact u19134
  · exact u19135
  · exact u19136
  · exact u19137

def r23887 : Route 9 := (fun mask => (mask,id))

def c23887 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23887 : Upper (D 8) (R 8) [6,96,264] 13 := by
  apply FastRouting.sound _ _ [6,96,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23887 c23887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19138
  · exact u19139
  · exact u19140
  · exact u19141
  · exact u19142
  · exact u19143
  · exact u19144
  · exact u19145
  · exact u19146
  · exact u19147

def r23888 : Route 9 := (fun mask => (mask,id))

def c23888 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23888 : Upper (D 8) (R 8) [6,96,288] 13 := by
  apply FastRouting.sound _ _ [6,96,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23888 c23888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19148
  · exact u19149
  · exact u19150
  · exact u19151
  · exact u19152
  · exact u19153
  · exact u19154
  · exact u19155
  · exact u19156
  · exact u19157

def b23889 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 324 185 185 185 249 185 441), lower := (rows 7 98 324 8 16 32 64 128 256), losses := [] }

theorem u23889 : Upper (D 8) (R 8) [6,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23890 : Route 9 := (fun mask => (mask,id))

def c23890 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23890 : Upper (D 8) (R 8) [6,96,384] 13 := by
  apply FastRouting.sound _ _ [6,96,384] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23890 c23890
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19158
  · exact u19159
  · exact u19160
  · exact u19161
  · exact u19162
  · exact u19163
  · exact u19164
  · exact u19165
  · exact u19166
  · exact u19167

def b23891 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 7 194 196 313 313 313 377 441 313), lower := (rows 7 194 196 8 16 32 64 128 256), losses := [] }

theorem u23891 : Upper (D 8) (R 8) [6,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23892 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23892 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23892 : Upper (D 8) (R 8) [6,192,257] 13 := by
  apply FastRouting.sound _ _ [6,192,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23892 c23892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19168
  · exact u19169
  · exact u19170
  · exact u19171
  · exact u19172
  · exact u19173
  · exact u19174

def r23893 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23893 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23893 : Upper (D 8) (R 8) [6,192,264] 13 := by
  apply FastRouting.sound _ _ [6,192,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23893 c23893
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19175
  · exact u19176
  · exact u19177
  · exact u19178
  · exact u19179
  · exact u19180
  · exact u19181

def r23894 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23894 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23894 : Upper (D 8) (R 8) [6,192,288] 13 := by
  apply FastRouting.sound _ _ [6,192,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23894 c23894
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19182
  · exact u19183
  · exact u19184
  · exact u19185
  · exact u19186
  · exact u19187
  · exact u19188

def b23895 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 7 194 324 185 185 185 249 185 441), lower := (rows 7 194 324 8 16 32 64 128 256), losses := [] }

theorem u23895 : Upper (D 8) (R 8) [6,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23896 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 13 504 496 496 496 496 496), lower := (rows 35 7 13 8 16 32 64 128 256), losses := [] }

theorem u23896 : Upper (D 8) (R 8) [34,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23897 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23897 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23897 : Upper (D 8) (R 8) [34,5,24] 13 := by
  apply FastRouting.sound _ _ [34,5,24] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r23897 c23897
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19189
  · exact u19190
  · exact u19191
  · exact u19192
  · exact u19193
  · exact u19194
  · exact u19195

def b23898 : PairBound 9 := { available := 504, camps := [{ cop := 5, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 37 504 504 504 504 504 504), lower := (rows 35 7 37 8 16 32 64 128 256), losses := [] }

theorem u23898 : Upper (D 8) (R 8) [34,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23899 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 44 505 497 497 497 497 497), lower := (rows 35 7 44 8 16 32 64 128 256), losses := [] }

theorem u23899 : Upper (D 8) (R 8) [34,5,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23900 : PairBound 9 := { available := 504, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 69 504 504 504 504 504 504), lower := (rows 35 7 69 8 16 32 64 128 256), losses := [] }

theorem u23900 : Upper (D 8) (R 8) [34,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23901 : Route 9 := (fun mask => (mask,id))

def c23901 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23901 : Upper (D 8) (R 8) [34,5,72] 13 := by
  apply FastRouting.sound _ _ [34,5,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23901 c23901
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19196
  · exact u19197
  · exact u19198
  · exact u19199
  · exact u19200
  · exact u19201
  · exact u19202
  · exact u19203
  · exact u19204
  · exact u19205
  · exact u19206
  · exact u19207
  · exact u19208
  · exact u19209
  · exact u19210

def b23902 : PairBound 9 := { available := 505, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 100 505 505 505 505 505 505), lower := (rows 35 7 100 8 16 32 64 128 256), losses := [] }

theorem u23902 : Upper (D 8) (R 8) [34,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23903 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23903 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23903 : Upper (D 8) (R 8) [34,5,192] 13 := by
  apply FastRouting.sound _ _ [34,5,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r23903 c23903
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19211
  · exact u19212
  · exact u19213
  · exact u19214
  · exact u19215
  · exact u19216
  · exact u19217
  · exact u19218
  · exact u19219
  · exact u19220
  · exact u19221

def b23904 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 261 248 248 248 248 248 504), lower := (rows 35 7 261 8 16 32 64 128 256), losses := [] }

theorem u23904 : Upper (D 8) (R 8) [34,5,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23905 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23905 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23905 : Upper (D 8) (R 8) [34,5,264] 13 := by
  apply FastRouting.sound _ _ [34,5,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23905 c23905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19222
  · exact u19223
  · exact u19224
  · exact u19225
  · exact u19226
  · exact u19227
  · exact u19228

def b23906 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 292 249 249 249 249 249 505), lower := (rows 35 7 292 8 16 32 64 128 256), losses := [] }

theorem u23906 : Upper (D 8) (R 8) [34,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23907 : Route 9 := (fun mask => (mask,id))

def c23907 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23907 : Upper (D 8) (R 8) [34,5,320] 13 := by
  apply FastRouting.sound _ _ [34,5,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23907 c23907
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19229
  · exact u19230
  · exact u19231
  · exact u19232
  · exact u19233
  · exact u19234
  · exact u19235
  · exact u19236
  · exact u19237
  · exact u19238

def r23908 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23908 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23908 : Upper (D 8) (R 8) [34,12,17] 13 := by
  apply FastRouting.sound _ _ [34,12,17] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r23908 c23908
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19239
  · exact u19240
  · exact u19241
  · exact u19242
  · exact u19243
  · exact u19244
  · exact u19245

def b23909 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 37 505 497 497 497 497 497), lower := (rows 35 14 37 8 16 32 64 128 256), losses := [] }

theorem u23909 : Upper (D 8) (R 8) [34,12,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23910_33 : Upper (D 8) (R 8) [34,12,48,33] 13 :=
  permutation_upper _ _ _ [34,12,33,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19246

def r23910 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23910 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23910 : Upper (D 8) (R 8) [34,12,48] 13 := by
  apply FastRouting.sound _ _ [34,12,48] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r23910 c23910
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23910_33
  · exact u19255
  · exact u19256
  · exact u19257
  · exact u19258
  · exact u19259
  · exact u19260

theorem m23911_17 : Upper (D 8) (R 8) [34,12,65,17] 13 :=
  permutation_upper _ _ _ [34,12,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19240

theorem m23911_33 : Upper (D 8) (R 8) [34,12,65,33] 13 :=
  permutation_upper _ _ _ [34,12,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19247

theorem m23911_48 : Upper (D 8) (R 8) [34,12,65,48] 13 :=
  permutation_upper _ _ _ [34,12,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19255

def r23911 : Route 9 := (fun mask => (mask,id))

def c23911 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23911 : Upper (D 8) (R 8) [34,12,65] 13 := by
  apply FastRouting.sound _ _ [34,12,65] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23911 c23911
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23911_17
  · exact m23911_33
  · exact m23911_48
  · exact u19261
  · exact u19262
  · exact u19263
  · exact u19264
  · exact u19265
  · exact u19266
  · exact u19267
  · exact u19268
  · exact u19269
  · exact u19270
  · exact u19271
  · exact u19272

theorem m23912_33 : Upper (D 8) (R 8) [34,12,80,33] 13 :=
  permutation_upper _ _ _ [34,12,33,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19248

theorem m23912_65 : Upper (D 8) (R 8) [34,12,80,65] 13 :=
  permutation_upper _ _ _ [34,12,65,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19262

theorem m23912_129 : Upper (D 8) (R 8) [34,12,80,129] 13 :=
  permutation_upper _ _ _ [34,12,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19265

def r23912 : Route 9 := (fun mask => (mask,id))

def c23912 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23912 : Upper (D 8) (R 8) [34,12,80] 13 := by
  apply FastRouting.sound _ _ [34,12,80] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r23912 c23912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23912_33
  · exact m23912_65
  · exact u19273
  · exact m23912_129
  · exact u19274
  · exact u19275
  · exact u19276
  · exact u19277
  · exact u19278
  · exact u19279

theorem m23913_17 : Upper (D 8) (R 8) [34,12,96,17] 13 :=
  permutation_upper _ _ _ [34,12,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19241

theorem m23913_33 : Upper (D 8) (R 8) [34,12,96,33] 13 :=
  permutation_upper _ _ _ [34,12,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19249

theorem m23913_48 : Upper (D 8) (R 8) [34,12,96,48] 13 :=
  permutation_upper _ _ _ [34,12,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19256

theorem m23913_65 : Upper (D 8) (R 8) [34,12,96,65] 13 :=
  permutation_upper _ _ _ [34,12,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19263

theorem m23913_80 : Upper (D 8) (R 8) [34,12,96,80] 13 :=
  permutation_upper _ _ _ [34,12,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19273

theorem m23913_129 : Upper (D 8) (R 8) [34,12,96,129] 13 :=
  permutation_upper _ _ _ [34,12,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19266

theorem m23913_144 : Upper (D 8) (R 8) [34,12,96,144] 13 :=
  permutation_upper _ _ _ [34,12,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19274

def r23913 : Route 9 := (fun mask => (mask,id))

def c23913 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23913 : Upper (D 8) (R 8) [34,12,96] 13 := by
  apply FastRouting.sound _ _ [34,12,96] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23913 c23913
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23913_17
  · exact m23913_33
  · exact m23913_48
  · exact m23913_65
  · exact m23913_80
  · exact u19280
  · exact m23913_129
  · exact m23913_144
  · exact u19281
  · exact u19282
  · exact u19283
  · exact u19284
  · exact u19285
  · exact u19286
  · exact u19287

theorem m23914_17 : Upper (D 8) (R 8) [34,12,192,17] 13 :=
  permutation_upper _ _ _ [34,12,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19242

theorem m23914_33 : Upper (D 8) (R 8) [34,12,192,33] 13 :=
  permutation_upper _ _ _ [34,12,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19250

theorem m23914_48 : Upper (D 8) (R 8) [34,12,192,48] 13 :=
  permutation_upper _ _ _ [34,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19257

theorem m23914_65 : Upper (D 8) (R 8) [34,12,192,65] 13 :=
  permutation_upper _ _ _ [34,12,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19267

theorem m23914_80 : Upper (D 8) (R 8) [34,12,192,80] 13 :=
  permutation_upper _ _ _ [34,12,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19275

theorem m23914_96 : Upper (D 8) (R 8) [34,12,192,96] 13 :=
  permutation_upper _ _ _ [34,12,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19282

def r23914 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23914 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23914 : Upper (D 8) (R 8) [34,12,192] 13 := by
  apply FastRouting.sound _ _ [34,12,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r23914 c23914
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23914_17
  · exact m23914_33
  · exact m23914_48
  · exact m23914_65
  · exact m23914_80
  · exact m23914_96
  · exact u19288
  · exact u19289
  · exact u19290
  · exact u19291
  · exact u19292

theorem m23915_17 : Upper (D 8) (R 8) [34,12,257,17] 13 :=
  permutation_upper _ _ _ [34,12,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19243

theorem m23915_33 : Upper (D 8) (R 8) [34,12,257,33] 13 :=
  permutation_upper _ _ _ [34,12,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19251

theorem m23915_48 : Upper (D 8) (R 8) [34,12,257,48] 13 :=
  permutation_upper _ _ _ [34,12,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19258

theorem m23915_65 : Upper (D 8) (R 8) [34,12,257,65] 13 :=
  permutation_upper _ _ _ [34,12,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19268

theorem m23915_80 : Upper (D 8) (R 8) [34,12,257,80] 13 :=
  permutation_upper _ _ _ [34,12,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19276

theorem m23915_96 : Upper (D 8) (R 8) [34,12,257,96] 13 :=
  permutation_upper _ _ _ [34,12,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19283

theorem m23915_192 : Upper (D 8) (R 8) [34,12,257,192] 13 :=
  permutation_upper _ _ _ [34,12,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19289

def r23915 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23915 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23915 : Upper (D 8) (R 8) [34,12,257] 13 := by
  apply FastRouting.sound _ _ [34,12,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23915 c23915
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23915_17
  · exact m23915_33
  · exact m23915_48
  · exact m23915_65
  · exact m23915_80
  · exact m23915_96
  · exact m23915_192

theorem m23916_33 : Upper (D 8) (R 8) [34,12,272,33] 13 :=
  permutation_upper _ _ _ [34,12,33,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19252

theorem m23916_65 : Upper (D 8) (R 8) [34,12,272,65] 13 :=
  permutation_upper _ _ _ [34,12,65,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19269

theorem m23916_96 : Upper (D 8) (R 8) [34,12,272,96] 13 :=
  permutation_upper _ _ _ [34,12,96,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19284

theorem m23916_192 : Upper (D 8) (R 8) [34,12,272,192] 13 :=
  permutation_upper _ _ _ [34,12,192,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19290

def r23916 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23916 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23916 : Upper (D 8) (R 8) [34,12,272] 13 := by
  apply FastRouting.sound _ _ [34,12,272] 13 (by decide) (choices 2) [33,65,96,192] r23916 c23916
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m23916_33
  · exact m23916_65
  · exact m23916_96
  · exact m23916_192

theorem m23917_17 : Upper (D 8) (R 8) [34,12,288,17] 13 :=
  permutation_upper _ _ _ [34,12,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19244

theorem m23917_33 : Upper (D 8) (R 8) [34,12,288,33] 13 :=
  permutation_upper _ _ _ [34,12,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19253

theorem m23917_48 : Upper (D 8) (R 8) [34,12,288,48] 13 :=
  permutation_upper _ _ _ [34,12,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19259

theorem m23917_65 : Upper (D 8) (R 8) [34,12,288,65] 13 :=
  permutation_upper _ _ _ [34,12,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19270

theorem m23917_80 : Upper (D 8) (R 8) [34,12,288,80] 13 :=
  permutation_upper _ _ _ [34,12,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19277

theorem m23917_96 : Upper (D 8) (R 8) [34,12,288,96] 13 :=
  permutation_upper _ _ _ [34,12,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19285

theorem m23917_192 : Upper (D 8) (R 8) [34,12,288,192] 13 :=
  permutation_upper _ _ _ [34,12,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19291

def r23917 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23917 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23917 : Upper (D 8) (R 8) [34,12,288] 13 := by
  apply FastRouting.sound _ _ [34,12,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23917 c23917
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23917_17
  · exact m23917_33
  · exact m23917_48
  · exact m23917_65
  · exact m23917_80
  · exact m23917_96
  · exact m23917_192

theorem m23918_17 : Upper (D 8) (R 8) [34,12,320,17] 13 :=
  permutation_upper _ _ _ [34,12,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19245

theorem m23918_33 : Upper (D 8) (R 8) [34,12,320,33] 13 :=
  permutation_upper _ _ _ [34,12,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19254

theorem m23918_48 : Upper (D 8) (R 8) [34,12,320,48] 13 :=
  permutation_upper _ _ _ [34,12,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19260

theorem m23918_65 : Upper (D 8) (R 8) [34,12,320,65] 13 :=
  permutation_upper _ _ _ [34,12,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19271

theorem m23918_80 : Upper (D 8) (R 8) [34,12,320,80] 13 :=
  permutation_upper _ _ _ [34,12,80,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19278

theorem m23918_96 : Upper (D 8) (R 8) [34,12,320,96] 13 :=
  permutation_upper _ _ _ [34,12,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19286

theorem m23918_129 : Upper (D 8) (R 8) [34,12,320,129] 13 :=
  permutation_upper _ _ _ [34,12,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19272

theorem m23918_144 : Upper (D 8) (R 8) [34,12,320,144] 13 :=
  permutation_upper _ _ _ [34,12,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19279

theorem m23918_160 : Upper (D 8) (R 8) [34,12,320,160] 13 :=
  permutation_upper _ _ _ [34,12,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19287

theorem m23918_192 : Upper (D 8) (R 8) [34,12,320,192] 13 :=
  permutation_upper _ _ _ [34,12,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19292

def r23918 : Route 9 := (fun mask => (mask,id))

def c23918 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23918 : Upper (D 8) (R 8) [34,12,320] 13 := by
  apply FastRouting.sound _ _ [34,12,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23918 c23918
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23918_17
  · exact m23918_33
  · exact m23918_48
  · exact m23918_65
  · exact m23918_80
  · exact m23918_96
  · exact m23918_129
  · exact m23918_144
  · exact m23918_160
  · exact m23918_192

def b23919 : PairBound 9 := { available := 500, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 508 500 500 500 500 500), lower := (rows 35 67 13 8 16 32 64 128 256), losses := [] }

theorem u23919 : Upper (D 8) (R 8) [34,65,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23920_5 : Upper (D 8) (R 8) [34,65,24,5] 13 :=
  permutation_upper _ _ _ [34,65,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19293

def r23920 : Route 9 := (fun mask => (mask,id))

def c23920 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23920 : Upper (D 8) (R 8) [34,65,24] 13 := by
  apply FastRouting.sound _ _ [34,65,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,257,260,288,320,384] r23920 c23920
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23920_5
  · exact u19312
  · exact u19313
  · exact u19314
  · exact u19315
  · exact u19316
  · exact u19317
  · exact u19318
  · exact u19319
  · exact u19320
  · exact u19321
  · exact u19322
  · exact u19323
  · exact u19324
  · exact u19325

def b23921 : PairBound 9 := { available := 508, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 37 508 508 508 508 508 508), lower := (rows 35 67 37 8 16 32 64 128 256), losses := [] }

theorem u23921 : Upper (D 8) (R 8) [34,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23922_5 : Upper (D 8) (R 8) [34,65,40,5] 13 :=
  permutation_upper _ _ _ [34,65,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19294

theorem m23922_17 : Upper (D 8) (R 8) [34,65,40,17] 13 :=
  permutation_upper _ _ _ [34,65,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19303

theorem m23922_20 : Upper (D 8) (R 8) [34,65,40,20] 13 :=
  permutation_upper _ _ _ [34,65,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19313

theorem m23922_33 : Upper (D 8) (R 8) [34,65,40,33] 13 :=
  permutation_upper _ _ _ [34,65,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19326

def r23922 : Route 9 := (fun mask => (mask,id))

def c23922 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u23922 : Upper (D 8) (R 8) [34,65,40] 13 := by
  apply FastRouting.sound _ _ [34,65,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r23922 c23922
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23922_5
  · exact m23922_17
  · exact m23922_20
  · exact m23922_33
  · exact u19335
  · exact u19336
  · exact u19337
  · exact u19338
  · exact u19339
  · exact u19340
  · exact u19341
  · exact u19342
  · exact u19343
  · exact u19344
  · exact u19345
  · exact u19346
  · exact u19347
  · exact u19348
  · exact u19349
  · exact u19350
  · exact u19351

def b23923 : PairBound 9 := { available := 444, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 444 444 444 508 444 444), lower := (rows 35 67 69 8 16 32 64 128 256), losses := [] }

theorem u23923 : Upper (D 8) (R 8) [34,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23924_5 : Upper (D 8) (R 8) [34,65,72,5] 13 :=
  permutation_upper _ _ _ [34,65,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19295

theorem m23924_17 : Upper (D 8) (R 8) [34,65,72,17] 13 :=
  permutation_upper _ _ _ [34,65,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19304

theorem m23924_20 : Upper (D 8) (R 8) [34,65,72,20] 13 :=
  permutation_upper _ _ _ [34,65,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19315

theorem m23924_33 : Upper (D 8) (R 8) [34,65,72,33] 13 :=
  permutation_upper _ _ _ [34,65,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19327

theorem m23924_36 : Upper (D 8) (R 8) [34,65,72,36] 13 :=
  permutation_upper _ _ _ [34,65,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19338

theorem m23924_48 : Upper (D 8) (R 8) [34,65,72,48] 13 :=
  permutation_upper _ _ _ [34,65,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19352

def r23924 : Route 9 := (fun mask => (mask,id))

def c23924 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u23924 : Upper (D 8) (R 8) [34,65,72] 13 := by
  apply FastRouting.sound _ _ [34,65,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r23924 c23924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23924_5
  · exact m23924_17
  · exact m23924_20
  · exact m23924_33
  · exact m23924_36
  · exact m23924_48
  · exact u19365
  · exact u19366
  · exact u19367
  · exact u19368
  · exact u19369
  · exact u19370
  · exact u19371
  · exact u19372
  · exact u19373

def b23925 : PairBound 9 := { available := 445, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 445 445 445 509 445 445), lower := (rows 35 67 100 8 16 32 64 128 256), losses := [] }

theorem u23925 : Upper (D 8) (R 8) [34,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23926 : PairBound 9 := { available := 508, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 508 508 508 508 508 508), lower := (rows 35 67 133 8 16 32 64 128 256), losses := [] }

theorem u23926 : Upper (D 8) (R 8) [34,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23927_5 : Upper (D 8) (R 8) [34,65,136,5] 13 :=
  permutation_upper _ _ _ [34,65,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19296

theorem m23927_17 : Upper (D 8) (R 8) [34,65,136,17] 13 :=
  permutation_upper _ _ _ [34,65,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19305

theorem m23927_20 : Upper (D 8) (R 8) [34,65,136,20] 13 :=
  permutation_upper _ _ _ [34,65,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19318

theorem m23927_33 : Upper (D 8) (R 8) [34,65,136,33] 13 :=
  permutation_upper _ _ _ [34,65,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19328

theorem m23927_36 : Upper (D 8) (R 8) [34,65,136,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19342

theorem m23927_48 : Upper (D 8) (R 8) [34,65,136,48] 13 :=
  permutation_upper _ _ _ [34,65,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19353

theorem m23927_65 : Upper (D 8) (R 8) [34,65,136,65] 13 :=
  permutation_upper _ _ _ [34,65,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19360

theorem m23927_68 : Upper (D 8) (R 8) [34,65,136,68] 13 :=
  permutation_upper _ _ _ [34,65,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19366

theorem m23927_80 : Upper (D 8) (R 8) [34,65,136,80] 13 :=
  permutation_upper _ _ _ [34,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19374

theorem m23927_96 : Upper (D 8) (R 8) [34,65,136,96] 13 :=
  permutation_upper _ _ _ [34,65,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19379

theorem m23927_129 : Upper (D 8) (R 8) [34,65,136,129] 13 :=
  permutation_upper _ _ _ [34,65,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19384

def r23927 : Route 9 := (fun mask => (mask,id))

def c23927 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u23927 : Upper (D 8) (R 8) [34,65,136] 13 := by
  apply FastRouting.sound _ _ [34,65,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r23927 c23927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23927_5
  · exact m23927_17
  · exact m23927_20
  · exact m23927_33
  · exact m23927_36
  · exact m23927_48
  · exact m23927_65
  · exact m23927_68
  · exact m23927_80
  · exact m23927_96
  · exact m23927_129
  · exact u19391
  · exact u19392
  · exact u19393
  · exact u19394
  · exact u19395
  · exact u19396
  · exact u19397
  · exact u19398
  · exact u19399
  · exact u19400

theorem m23928_5 : Upper (D 8) (R 8) [34,65,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19297

theorem m23928_17 : Upper (D 8) (R 8) [34,65,160,17] 13 :=
  permutation_upper _ _ _ [34,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19306

theorem m23928_20 : Upper (D 8) (R 8) [34,65,160,20] 13 :=
  permutation_upper _ _ _ [34,65,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19319

theorem m23928_33 : Upper (D 8) (R 8) [34,65,160,33] 13 :=
  permutation_upper _ _ _ [34,65,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19329

theorem m23928_36 : Upper (D 8) (R 8) [34,65,160,36] 13 :=
  permutation_upper _ _ _ [34,65,40,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19344

theorem m23928_48 : Upper (D 8) (R 8) [34,65,160,48] 13 :=
  permutation_upper _ _ _ [34,65,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19354

theorem m23928_65 : Upper (D 8) (R 8) [34,65,160,65] 13 :=
  permutation_upper _ _ _ [34,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19361

theorem m23928_68 : Upper (D 8) (R 8) [34,65,160,68] 13 :=
  permutation_upper _ _ _ [34,65,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19368

theorem m23928_80 : Upper (D 8) (R 8) [34,65,160,80] 13 :=
  permutation_upper _ _ _ [34,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19375

theorem m23928_96 : Upper (D 8) (R 8) [34,65,160,96] 13 :=
  permutation_upper _ _ _ [34,65,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19380

theorem m23928_129 : Upper (D 8) (R 8) [34,65,160,129] 13 :=
  permutation_upper _ _ _ [34,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19385

theorem m23928_132 : Upper (D 8) (R 8) [34,65,160,132] 13 :=
  permutation_upper _ _ _ [34,65,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19393

theorem m23928_144 : Upper (D 8) (R 8) [34,65,160,144] 13 :=
  permutation_upper _ _ _ [34,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19401

def r23928 : Route 9 := (fun mask => (mask,id))

def c23928 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u23928 : Upper (D 8) (R 8) [34,65,160] 13 := by
  apply FastRouting.sound _ _ [34,65,160] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r23928 c23928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23928_5
  · exact m23928_17
  · exact m23928_20
  · exact m23928_33
  · exact m23928_36
  · exact m23928_48
  · exact m23928_65
  · exact m23928_68
  · exact m23928_80
  · exact m23928_96
  · exact m23928_129
  · exact m23928_132
  · exact m23928_144
  · exact u19407
  · exact u19408
  · exact u19409
  · exact u19410
  · exact u19411
  · exact u19412
  · exact u19413
  · exact u19414

theorem m23929_5 : Upper (D 8) (R 8) [34,65,192,5] 13 :=
  permutation_upper _ _ _ [34,65,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19298

theorem m23929_17 : Upper (D 8) (R 8) [34,65,192,17] 13 :=
  permutation_upper _ _ _ [34,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19307

theorem m23929_20 : Upper (D 8) (R 8) [34,65,192,20] 13 :=
  permutation_upper _ _ _ [34,65,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19320

theorem m23929_33 : Upper (D 8) (R 8) [34,65,192,33] 13 :=
  permutation_upper _ _ _ [34,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19330

theorem m23929_36 : Upper (D 8) (R 8) [34,65,192,36] 13 :=
  permutation_upper _ _ _ [34,65,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19345

theorem m23929_48 : Upper (D 8) (R 8) [34,65,192,48] 13 :=
  permutation_upper _ _ _ [34,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19355

theorem m23929_129 : Upper (D 8) (R 8) [34,65,192,129] 13 :=
  permutation_upper _ _ _ [34,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19386

theorem m23929_132 : Upper (D 8) (R 8) [34,65,192,132] 13 :=
  permutation_upper _ _ _ [34,65,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19394

theorem m23929_144 : Upper (D 8) (R 8) [34,65,192,144] 13 :=
  permutation_upper _ _ _ [34,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19402

theorem m23929_160 : Upper (D 8) (R 8) [34,65,192,160] 13 :=
  permutation_upper _ _ _ [34,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19408

def r23929 : Route 9 := (fun mask => (mask,id))

def c23929 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u23929 : Upper (D 8) (R 8) [34,65,192] 13 := by
  apply FastRouting.sound _ _ [34,65,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r23929 c23929
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23929_5
  · exact m23929_17
  · exact m23929_20
  · exact m23929_33
  · exact m23929_36
  · exact m23929_48
  · exact m23929_129
  · exact m23929_132
  · exact m23929_144
  · exact m23929_160
  · exact u19415
  · exact u19416
  · exact u19417
  · exact u19418
  · exact u19419

def b23930 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 261 252 252 252 252 252 508), lower := (rows 35 67 261 8 16 32 64 128 256), losses := [] }

theorem u23930 : Upper (D 8) (R 8) [34,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23931_5 : Upper (D 8) (R 8) [34,65,264,5] 13 :=
  permutation_upper _ _ _ [34,65,9,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19299

theorem m23931_17 : Upper (D 8) (R 8) [34,65,264,17] 13 :=
  permutation_upper _ _ _ [34,65,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19308

theorem m23931_20 : Upper (D 8) (R 8) [34,65,264,20] 13 :=
  permutation_upper _ _ _ [34,65,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19322

theorem m23931_33 : Upper (D 8) (R 8) [34,65,264,33] 13 :=
  permutation_upper _ _ _ [34,65,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19331

theorem m23931_36 : Upper (D 8) (R 8) [34,65,264,36] 13 :=
  permutation_upper _ _ _ [34,65,40,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19347

theorem m23931_48 : Upper (D 8) (R 8) [34,65,264,48] 13 :=
  permutation_upper _ _ _ [34,65,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19356

theorem m23931_65 : Upper (D 8) (R 8) [34,65,264,65] 13 :=
  permutation_upper _ _ _ [34,65,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19362

theorem m23931_68 : Upper (D 8) (R 8) [34,65,264,68] 13 :=
  permutation_upper _ _ _ [34,65,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19370

theorem m23931_80 : Upper (D 8) (R 8) [34,65,264,80] 13 :=
  permutation_upper _ _ _ [34,65,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19376

theorem m23931_96 : Upper (D 8) (R 8) [34,65,264,96] 13 :=
  permutation_upper _ _ _ [34,65,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19381

theorem m23931_129 : Upper (D 8) (R 8) [34,65,264,129] 13 :=
  permutation_upper _ _ _ [34,65,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19387

theorem m23931_132 : Upper (D 8) (R 8) [34,65,264,132] 13 :=
  permutation_upper _ _ _ [34,65,136,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19396

theorem m23931_144 : Upper (D 8) (R 8) [34,65,264,144] 13 :=
  permutation_upper _ _ _ [34,65,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19403

theorem m23931_160 : Upper (D 8) (R 8) [34,65,264,160] 13 :=
  permutation_upper _ _ _ [34,65,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19410

theorem m23931_192 : Upper (D 8) (R 8) [34,65,264,192] 13 :=
  permutation_upper _ _ _ [34,65,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19416

def r23931 : Route 9 := (fun mask => (mask,id))

def c23931 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23931 : Upper (D 8) (R 8) [34,65,264] 13 := by
  apply FastRouting.sound _ _ [34,65,264] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23931 c23931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23931_5
  · exact m23931_17
  · exact m23931_20
  · exact m23931_33
  · exact m23931_36
  · exact m23931_48
  · exact m23931_65
  · exact m23931_68
  · exact m23931_80
  · exact m23931_96
  · exact m23931_129
  · exact m23931_132
  · exact m23931_144
  · exact m23931_160
  · exact m23931_192

theorem m23932_5 : Upper (D 8) (R 8) [34,65,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19300

theorem m23932_17 : Upper (D 8) (R 8) [34,65,288,17] 13 :=
  permutation_upper _ _ _ [34,65,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19309

theorem m23932_20 : Upper (D 8) (R 8) [34,65,288,20] 13 :=
  permutation_upper _ _ _ [34,65,24,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19323

theorem m23932_33 : Upper (D 8) (R 8) [34,65,288,33] 13 :=
  permutation_upper _ _ _ [34,65,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19332

theorem m23932_36 : Upper (D 8) (R 8) [34,65,288,36] 13 :=
  permutation_upper _ _ _ [34,65,40,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19349

theorem m23932_48 : Upper (D 8) (R 8) [34,65,288,48] 13 :=
  permutation_upper _ _ _ [34,65,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19357

theorem m23932_65 : Upper (D 8) (R 8) [34,65,288,65] 13 :=
  permutation_upper _ _ _ [34,65,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19363

theorem m23932_68 : Upper (D 8) (R 8) [34,65,288,68] 13 :=
  permutation_upper _ _ _ [34,65,72,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19372

theorem m23932_80 : Upper (D 8) (R 8) [34,65,288,80] 13 :=
  permutation_upper _ _ _ [34,65,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19377

theorem m23932_96 : Upper (D 8) (R 8) [34,65,288,96] 13 :=
  permutation_upper _ _ _ [34,65,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19382

theorem m23932_129 : Upper (D 8) (R 8) [34,65,288,129] 13 :=
  permutation_upper _ _ _ [34,65,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19388

theorem m23932_132 : Upper (D 8) (R 8) [34,65,288,132] 13 :=
  permutation_upper _ _ _ [34,65,136,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19398

theorem m23932_144 : Upper (D 8) (R 8) [34,65,288,144] 13 :=
  permutation_upper _ _ _ [34,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19404

theorem m23932_160 : Upper (D 8) (R 8) [34,65,288,160] 13 :=
  permutation_upper _ _ _ [34,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19412

theorem m23932_192 : Upper (D 8) (R 8) [34,65,288,192] 13 :=
  permutation_upper _ _ _ [34,65,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19418

def r23932 : Route 9 := (fun mask => (mask,id))

def c23932 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23932 : Upper (D 8) (R 8) [34,65,288] 13 := by
  apply FastRouting.sound _ _ [34,65,288] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23932 c23932
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23932_5
  · exact m23932_17
  · exact m23932_20
  · exact m23932_33
  · exact m23932_36
  · exact m23932_48
  · exact m23932_65
  · exact m23932_68
  · exact m23932_80
  · exact m23932_96
  · exact m23932_129
  · exact m23932_132
  · exact m23932_144
  · exact m23932_160
  · exact m23932_192

theorem m23933_5 : Upper (D 8) (R 8) [34,65,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19301

theorem m23933_17 : Upper (D 8) (R 8) [34,65,320,17] 13 :=
  permutation_upper _ _ _ [34,65,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19310

theorem m23933_20 : Upper (D 8) (R 8) [34,65,320,20] 13 :=
  permutation_upper _ _ _ [34,65,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19324

theorem m23933_33 : Upper (D 8) (R 8) [34,65,320,33] 13 :=
  permutation_upper _ _ _ [34,65,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19333

theorem m23933_36 : Upper (D 8) (R 8) [34,65,320,36] 13 :=
  permutation_upper _ _ _ [34,65,40,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19350

theorem m23933_48 : Upper (D 8) (R 8) [34,65,320,48] 13 :=
  permutation_upper _ _ _ [34,65,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19358

theorem m23933_129 : Upper (D 8) (R 8) [34,65,320,129] 13 :=
  permutation_upper _ _ _ [34,65,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19389

theorem m23933_132 : Upper (D 8) (R 8) [34,65,320,132] 13 :=
  permutation_upper _ _ _ [34,65,136,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19399

theorem m23933_144 : Upper (D 8) (R 8) [34,65,320,144] 13 :=
  permutation_upper _ _ _ [34,65,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19405

theorem m23933_160 : Upper (D 8) (R 8) [34,65,320,160] 13 :=
  permutation_upper _ _ _ [34,65,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19413

def r23933 : Route 9 := (fun mask => (mask,id))

def c23933 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23933 : Upper (D 8) (R 8) [34,65,320] 13 := by
  apply FastRouting.sound _ _ [34,65,320] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r23933 c23933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23933_5
  · exact m23933_17
  · exact m23933_20
  · exact m23933_33
  · exact m23933_36
  · exact m23933_48
  · exact m23933_129
  · exact m23933_132
  · exact m23933_144
  · exact m23933_160

theorem m23934_5 : Upper (D 8) (R 8) [34,65,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19302

theorem m23934_17 : Upper (D 8) (R 8) [34,65,384,17] 13 :=
  permutation_upper _ _ _ [34,65,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19311

theorem m23934_20 : Upper (D 8) (R 8) [34,65,384,20] 13 :=
  permutation_upper _ _ _ [34,65,24,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19325

theorem m23934_33 : Upper (D 8) (R 8) [34,65,384,33] 13 :=
  permutation_upper _ _ _ [34,65,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19334

theorem m23934_36 : Upper (D 8) (R 8) [34,65,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19351

theorem m23934_48 : Upper (D 8) (R 8) [34,65,384,48] 13 :=
  permutation_upper _ _ _ [34,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19359

theorem m23934_65 : Upper (D 8) (R 8) [34,65,384,65] 13 :=
  permutation_upper _ _ _ [34,65,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19364

theorem m23934_68 : Upper (D 8) (R 8) [34,65,384,68] 13 :=
  permutation_upper _ _ _ [34,65,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19373

theorem m23934_80 : Upper (D 8) (R 8) [34,65,384,80] 13 :=
  permutation_upper _ _ _ [34,65,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19378

theorem m23934_96 : Upper (D 8) (R 8) [34,65,384,96] 13 :=
  permutation_upper _ _ _ [34,65,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19383

theorem m23934_129 : Upper (D 8) (R 8) [34,65,384,129] 13 :=
  permutation_upper _ _ _ [34,65,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19390

theorem m23934_132 : Upper (D 8) (R 8) [34,65,384,132] 13 :=
  permutation_upper _ _ _ [34,65,136,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19400

theorem m23934_144 : Upper (D 8) (R 8) [34,65,384,144] 13 :=
  permutation_upper _ _ _ [34,65,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19406

theorem m23934_160 : Upper (D 8) (R 8) [34,65,384,160] 13 :=
  permutation_upper _ _ _ [34,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19414

theorem m23934_192 : Upper (D 8) (R 8) [34,65,384,192] 13 :=
  permutation_upper _ _ _ [34,65,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19419

def r23934 : Route 9 := (fun mask => (mask,id))

def c23934 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23934 : Upper (D 8) (R 8) [34,65,384] 13 := by
  apply FastRouting.sound _ _ [34,65,384] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23934 c23934
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23934_5
  · exact m23934_17
  · exact m23934_20
  · exact m23934_33
  · exact m23934_36
  · exact m23934_48
  · exact m23934_65
  · exact m23934_68
  · exact m23934_80
  · exact m23934_96
  · exact m23934_129
  · exact m23934_132
  · exact m23934_144
  · exact m23934_160
  · exact m23934_192

def r23935 : Route 9 := (fun mask => (mask,id))

def c23935 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23935 : Upper (D 8) (R 8) [34,68,9] 13 := by
  apply FastRouting.sound _ _ [34,68,9] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23935 c23935
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19420
  · exact u19421
  · exact u19422
  · exact u19423
  · exact u19424
  · exact u19425
  · exact u19426
  · exact u19427
  · exact u19428
  · exact u19429
  · exact u19430
  · exact u19431
  · exact u19432
  · exact u19433
  · exact u19434

def r23936 : Route 9 := (fun mask => (mask,id))

def c23936 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23936 : Upper (D 8) (R 8) [34,68,24] 13 := by
  apply FastRouting.sound _ _ [34,68,24] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r23936 c23936
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19435
  · exact u19436
  · exact u19437
  · exact u19438
  · exact u19439
  · exact u19440
  · exact u19441
  · exact u19442
  · exact u19443
  · exact u19444

def b23937 : PairBound 9 := { available := 505, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 37 505 505 505 505 505 505), lower := (rows 35 70 37 8 16 32 64 128 256), losses := [] }

theorem u23937 : Upper (D 8) (R 8) [34,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23938 : Route 9 := (fun mask => (mask,id))

def c23938 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23938 : Upper (D 8) (R 8) [34,68,40] 13 := by
  apply FastRouting.sound _ _ [34,68,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23938 c23938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19445
  · exact u19446
  · exact u19447
  · exact u19448
  · exact u19449
  · exact u19450
  · exact u19451
  · exact u19452
  · exact u19453
  · exact u19454
  · exact u19455
  · exact u19456
  · exact u19457
  · exact u19458
  · exact u19459

def b23939 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 69 441 441 441 505 441 441), lower := (rows 35 70 69 8 16 32 64 128 256), losses := [] }

theorem u23939 : Upper (D 8) (R 8) [34,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u23939
end Delivery.IrregularNine14.P08
