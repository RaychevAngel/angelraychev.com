import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0049
import IrregularNine14P03C0050
import IrregularNine14P03C0051
import IrregularNine14P03C0052
import IrregularNine14P03C0053
import IrregularNine14P03C0054
import IrregularNine14P03C0055

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6120 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 76 401 433 465 401 401), lower := (rows 35 67 44 76 16 32 64 128 256), losses := [] }

theorem u6120 : Upper (D 3) (R 3) [34,65,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6120
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6121_5 : Upper (D 3) (R 3) [34,65,40,80,5] 13 :=
  permutation_upper _ _ _ [34,65,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2958

def r6121 : Route 9 := (fun mask => (mask,id))

def c6121 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6121 : Upper (D 3) (R 3) [34,65,40,80] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80] 13 (by decide) (choices 2) [5,129,132,257,260,384] r6121 c6121
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6121_5
  · exact u3166
  · exact u3167
  · exact u3168
  · exact u3169
  · exact u3170

theorem m6122_5 : Upper (D 3) (R 3) [34,65,40,129,5] 13 :=
  permutation_upper _ _ _ [34,65,9,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2959

def r6122 : Route 9 := (fun mask => (mask,id))

def c6122 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6122 : Upper (D 3) (R 3) [34,65,40,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129] 13 (by decide) (choices 2) [5,65,68,129,132,192,257,260,320,384] r6122 c6122
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6122_5
  · exact u3171
  · exact u3172
  · exact u3173
  · exact u3174
  · exact u3175
  · exact u3176
  · exact u3177
  · exact u3178
  · exact u3179

def b6123 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 140 465 497 465 465 465), lower := (rows 35 67 44 140 16 32 64 128 256), losses := [] }

theorem u6123 : Upper (D 3) (R 3) [34,65,40,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6123
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6124_5 : Upper (D 3) (R 3) [34,65,40,144,5] 13 :=
  permutation_upper _ _ _ [34,65,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2960

def r6124 : Route 9 := (fun mask => (mask,id))

def c6124 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6124 : Upper (D 3) (R 3) [34,65,40,144] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144] 13 (by decide) (choices 2) [5,65,68,129,132,192,257,260,320,384] r6124 c6124
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6124_5
  · exact u3185
  · exact u3186
  · exact u3187
  · exact u3188
  · exact u3189
  · exact u3190
  · exact u3191
  · exact u3192
  · exact u3193

theorem m6125_5 : Upper (D 3) (R 3) [34,65,40,192,5] 13 :=
  permutation_upper _ _ _ [34,65,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2961

def r6125 : Route 9 := (fun mask => (mask,id))

def c6125 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6125 : Upper (D 3) (R 3) [34,65,40,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192] 13 (by decide) (choices 2) [5,129,132,257,260,384] r6125 c6125
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6125_5
  · exact u3194
  · exact u3195
  · exact u3196
  · exact u3197
  · exact u3198

theorem m6126_5 : Upper (D 3) (R 3) [34,65,40,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2962

def r6126 : Route 9 := (fun mask => (mask,id))

def c6126 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6126 : Upper (D 3) (R 3) [34,65,40,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257] 13 (by decide) (choices 2) [5,65,68,129,132,192] r6126 c6126
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6126_5
  · exact u3199
  · exact u3200
  · exact u3201
  · exact u3202
  · exact u3203

def b6127 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 268 209 241 209 209 465), lower := (rows 35 67 44 268 16 32 64 128 256), losses := [] }

theorem u6127 : Upper (D 3) (R 3) [34,65,40,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6127
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6128_5 : Upper (D 3) (R 3) [34,65,40,272,5] 13 :=
  permutation_upper _ _ _ [34,65,9,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2963

def r6128 : Route 9 := (fun mask => (mask,id))

def c6128 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6128 : Upper (D 3) (R 3) [34,65,40,272] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272] 13 (by decide) (choices 2) [5,65,68,129,132,192] r6128 c6128
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6128_5
  · exact u3206
  · exact u3207
  · exact u3208
  · exact u3209
  · exact u3210

theorem m6129_5 : Upper (D 3) (R 3) [34,65,40,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2964

def r6129 : Route 9 := (fun mask => (mask,id))

def c6129 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6129 : Upper (D 3) (R 3) [34,65,40,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320] 13 (by decide) (choices 2) [5,129,132] r6129 c6129
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6129_5
  · exact u3211
  · exact u3212

theorem m6130_5 : Upper (D 3) (R 3) [34,65,40,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2965

def r6130 : Route 9 := (fun mask => (mask,id))

def c6130 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6130 : Upper (D 3) (R 3) [34,65,40,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384] 13 (by decide) (choices 2) [5,65,68,129,132,192] r6130 c6130
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6130_5
  · exact u3213
  · exact u3214
  · exact u3215
  · exact u3216
  · exact u3217

theorem m6131_9 : Upper (D 3) (R 3) [34,65,48,68,9] 13 :=
  permutation_upper _ _ _ [34,65,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2977

theorem m6131_129 : Upper (D 3) (R 3) [34,65,48,68,129] 13 :=
  permutation_upper _ _ _ [34,65,40,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3172

theorem m6131_136 : Upper (D 3) (R 3) [34,65,48,68,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3186

theorem m6131_257 : Upper (D 3) (R 3) [34,65,48,68,257] 13 :=
  permutation_upper _ _ _ [34,65,40,257,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3200

theorem m6131_264 : Upper (D 3) (R 3) [34,65,48,68,264] 13 :=
  permutation_upper _ _ _ [34,65,40,272,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3207

theorem m6131_384 : Upper (D 3) (R 3) [34,65,48,68,384] 13 :=
  permutation_upper _ _ _ [34,65,40,384,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3214

def r6131 : Route 9 := (fun mask => (mask,id))

def c6131 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6131 : Upper (D 3) (R 3) [34,65,48,68] 13 := by
  apply FastRouting.sound _ _ [34,65,48,68] 13 (by decide) (choices 2) [9,129,136,257,264,384] r6131 c6131
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6131_9
  · exact m6131_129
  · exact m6131_136
  · exact m6131_257
  · exact m6131_264
  · exact m6131_384

theorem m6132_5 : Upper (D 3) (R 3) [34,65,48,129,5] 13 :=
  permutation_upper _ _ _ [34,65,9,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2953

theorem m6132_9 : Upper (D 3) (R 3) [34,65,48,129,9] 13 :=
  permutation_upper _ _ _ [34,65,9,129,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2990

theorem m6132_12 : Upper (D 3) (R 3) [34,65,48,129,12] 13 :=
  permutation_upper _ _ _ [34,65,24,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3083

theorem m6132_65 : Upper (D 3) (R 3) [34,65,48,129,65] 13 :=
  permutation_upper _ _ _ [34,65,40,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3158

theorem m6132_68 : Upper (D 3) (R 3) [34,65,48,129,68] 13 :=
  permutation_upper _ _ _ [34,65,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3163

theorem m6132_72 : Upper (D 3) (R 3) [34,65,48,129,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3166

theorem m6132_129 : Upper (D 3) (R 3) [34,65,48,129,129] 13 :=
  permutation_upper _ _ _ [34,65,40,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3173

theorem m6132_132 : Upper (D 3) (R 3) [34,65,48,129,132] 13 :=
  permutation_upper _ _ _ [34,65,40,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3180

theorem m6132_136 : Upper (D 3) (R 3) [34,65,48,129,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3187

theorem m6132_192 : Upper (D 3) (R 3) [34,65,48,129,192] 13 :=
  permutation_upper _ _ _ [34,65,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3194

theorem m6132_257 : Upper (D 3) (R 3) [34,65,48,129,257] 13 :=
  permutation_upper _ _ _ [34,65,40,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3201

theorem m6132_260 : Upper (D 3) (R 3) [34,65,48,129,260] 13 :=
  permutation_upper _ _ _ [34,65,40,260,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3204

theorem m6132_264 : Upper (D 3) (R 3) [34,65,48,129,264] 13 :=
  permutation_upper _ _ _ [34,65,40,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3208

theorem m6132_320 : Upper (D 3) (R 3) [34,65,48,129,320] 13 :=
  permutation_upper _ _ _ [34,65,40,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3211

theorem m6132_384 : Upper (D 3) (R 3) [34,65,48,129,384] 13 :=
  permutation_upper _ _ _ [34,65,40,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3215

def r6132 : Route 9 := (fun mask => (mask,id))

def c6132 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6132 : Upper (D 3) (R 3) [34,65,48,129] 13 := by
  apply FastRouting.sound _ _ [34,65,48,129] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192,257,260,264,320,384] r6132 c6132
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6132_5
  · exact m6132_9
  · exact m6132_12
  · exact m6132_65
  · exact m6132_68
  · exact m6132_72
  · exact m6132_129
  · exact m6132_132
  · exact m6132_136
  · exact m6132_192
  · exact m6132_257
  · exact m6132_260
  · exact m6132_264
  · exact m6132_320
  · exact m6132_384

theorem m6133_9 : Upper (D 3) (R 3) [34,65,48,132,9] 13 :=
  permutation_upper _ _ _ [34,65,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3010

theorem m6133_65 : Upper (D 3) (R 3) [34,65,48,132,65] 13 :=
  permutation_upper _ _ _ [34,65,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3159

theorem m6133_72 : Upper (D 3) (R 3) [34,65,48,132,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3167

theorem m6133_129 : Upper (D 3) (R 3) [34,65,48,132,129] 13 :=
  permutation_upper _ _ _ [34,65,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3174

theorem m6133_136 : Upper (D 3) (R 3) [34,65,48,132,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3188

theorem m6133_192 : Upper (D 3) (R 3) [34,65,48,132,192] 13 :=
  permutation_upper _ _ _ [34,65,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3195

theorem m6133_257 : Upper (D 3) (R 3) [34,65,48,132,257] 13 :=
  permutation_upper _ _ _ [34,65,40,257,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3202

theorem m6133_264 : Upper (D 3) (R 3) [34,65,48,132,264] 13 :=
  permutation_upper _ _ _ [34,65,40,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3209

theorem m6133_320 : Upper (D 3) (R 3) [34,65,48,132,320] 13 :=
  permutation_upper _ _ _ [34,65,40,320,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3212

theorem m6133_384 : Upper (D 3) (R 3) [34,65,48,132,384] 13 :=
  permutation_upper _ _ _ [34,65,40,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3216

def r6133 : Route 9 := (fun mask => (mask,id))

def c6133 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6133 : Upper (D 3) (R 3) [34,65,48,132] 13 := by
  apply FastRouting.sound _ _ [34,65,48,132] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r6133 c6133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6133_9
  · exact m6133_65
  · exact m6133_72
  · exact m6133_129
  · exact m6133_136
  · exact m6133_192
  · exact m6133_257
  · exact m6133_264
  · exact m6133_320
  · exact m6133_384

theorem m6134_5 : Upper (D 3) (R 3) [34,65,48,192,5] 13 :=
  permutation_upper _ _ _ [34,65,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2954

theorem m6134_9 : Upper (D 3) (R 3) [34,65,48,192,9] 13 :=
  permutation_upper _ _ _ [34,65,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3031

theorem m6134_12 : Upper (D 3) (R 3) [34,65,48,192,12] 13 :=
  permutation_upper _ _ _ [34,65,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3084

theorem m6134_129 : Upper (D 3) (R 3) [34,65,48,192,129] 13 :=
  permutation_upper _ _ _ [34,65,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3175

theorem m6134_132 : Upper (D 3) (R 3) [34,65,48,192,132] 13 :=
  permutation_upper _ _ _ [34,65,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3181

theorem m6134_136 : Upper (D 3) (R 3) [34,65,48,192,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3189

theorem m6134_257 : Upper (D 3) (R 3) [34,65,48,192,257] 13 :=
  permutation_upper _ _ _ [34,65,40,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3203

theorem m6134_260 : Upper (D 3) (R 3) [34,65,48,192,260] 13 :=
  permutation_upper _ _ _ [34,65,40,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3205

theorem m6134_264 : Upper (D 3) (R 3) [34,65,48,192,264] 13 :=
  permutation_upper _ _ _ [34,65,40,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3210

theorem m6134_384 : Upper (D 3) (R 3) [34,65,48,192,384] 13 :=
  permutation_upper _ _ _ [34,65,40,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3217

def r6134 : Route 9 := (fun mask => (mask,id))

def c6134 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6134 : Upper (D 3) (R 3) [34,65,48,192] 13 := by
  apply FastRouting.sound _ _ [34,65,48,192] 13 (by decide) (choices 2) [5,9,12,129,132,136,257,260,264,384] r6134 c6134
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6134_5
  · exact m6134_9
  · exact m6134_12
  · exact m6134_129
  · exact m6134_132
  · exact m6134_136
  · exact m6134_257
  · exact m6134_260
  · exact m6134_264
  · exact m6134_384

theorem m6135_5 : Upper (D 3) (R 3) [34,65,48,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,36,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2955

theorem m6135_9 : Upper (D 3) (R 3) [34,65,48,257,9] 13 :=
  permutation_upper _ _ _ [34,65,9,257,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3039

theorem m6135_12 : Upper (D 3) (R 3) [34,65,48,257,12] 13 :=
  permutation_upper _ _ _ [34,65,24,36,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3085

theorem m6135_65 : Upper (D 3) (R 3) [34,65,48,257,65] 13 :=
  permutation_upper _ _ _ [34,65,40,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3160

theorem m6135_68 : Upper (D 3) (R 3) [34,65,48,257,68] 13 :=
  permutation_upper _ _ _ [34,65,40,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3164

theorem m6135_72 : Upper (D 3) (R 3) [34,65,48,257,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3168

theorem m6135_129 : Upper (D 3) (R 3) [34,65,48,257,129] 13 :=
  permutation_upper _ _ _ [34,65,40,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3176

theorem m6135_132 : Upper (D 3) (R 3) [34,65,48,257,132] 13 :=
  permutation_upper _ _ _ [34,65,40,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3182

theorem m6135_136 : Upper (D 3) (R 3) [34,65,48,257,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3190

theorem m6135_192 : Upper (D 3) (R 3) [34,65,48,257,192] 13 :=
  permutation_upper _ _ _ [34,65,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3196

def r6135 : Route 9 := (fun mask => (mask,id))

def c6135 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6135 : Upper (D 3) (R 3) [34,65,48,257] 13 := by
  apply FastRouting.sound _ _ [34,65,48,257] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r6135 c6135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6135_5
  · exact m6135_9
  · exact m6135_12
  · exact m6135_65
  · exact m6135_68
  · exact m6135_72
  · exact m6135_129
  · exact m6135_132
  · exact m6135_136
  · exact m6135_192

theorem m6136_9 : Upper (D 3) (R 3) [34,65,48,260,9] 13 :=
  permutation_upper _ _ _ [34,65,9,272,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3051

theorem m6136_65 : Upper (D 3) (R 3) [34,65,48,260,65] 13 :=
  permutation_upper _ _ _ [34,65,40,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3161

theorem m6136_72 : Upper (D 3) (R 3) [34,65,48,260,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3169

theorem m6136_129 : Upper (D 3) (R 3) [34,65,48,260,129] 13 :=
  permutation_upper _ _ _ [34,65,40,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3177

theorem m6136_136 : Upper (D 3) (R 3) [34,65,48,260,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3191

theorem m6136_192 : Upper (D 3) (R 3) [34,65,48,260,192] 13 :=
  permutation_upper _ _ _ [34,65,40,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3197

def r6136 : Route 9 := (fun mask => (mask,id))

def c6136 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6136 : Upper (D 3) (R 3) [34,65,48,260] 13 := by
  apply FastRouting.sound _ _ [34,65,48,260] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6136 c6136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6136_9
  · exact m6136_65
  · exact m6136_72
  · exact m6136_129
  · exact m6136_136
  · exact m6136_192

theorem m6137_5 : Upper (D 3) (R 3) [34,65,48,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2956

theorem m6137_9 : Upper (D 3) (R 3) [34,65,48,320,9] 13 :=
  permutation_upper _ _ _ [34,65,9,320,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3063

theorem m6137_12 : Upper (D 3) (R 3) [34,65,48,320,12] 13 :=
  permutation_upper _ _ _ [34,65,24,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3086

theorem m6137_129 : Upper (D 3) (R 3) [34,65,48,320,129] 13 :=
  permutation_upper _ _ _ [34,65,40,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3178

theorem m6137_132 : Upper (D 3) (R 3) [34,65,48,320,132] 13 :=
  permutation_upper _ _ _ [34,65,40,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3183

theorem m6137_136 : Upper (D 3) (R 3) [34,65,48,320,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3192

def r6137 : Route 9 := (fun mask => (mask,id))

def c6137 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6137 : Upper (D 3) (R 3) [34,65,48,320] 13 := by
  apply FastRouting.sound _ _ [34,65,48,320] 13 (by decide) (choices 2) [5,9,12,129,132,136] r6137 c6137
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6137_5
  · exact m6137_9
  · exact m6137_12
  · exact m6137_129
  · exact m6137_132
  · exact m6137_136

theorem m6138_5 : Upper (D 3) (R 3) [34,65,48,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2957

theorem m6138_9 : Upper (D 3) (R 3) [34,65,48,384,9] 13 :=
  permutation_upper _ _ _ [34,65,9,384,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3068

theorem m6138_12 : Upper (D 3) (R 3) [34,65,48,384,12] 13 :=
  permutation_upper _ _ _ [34,65,24,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3087

theorem m6138_65 : Upper (D 3) (R 3) [34,65,48,384,65] 13 :=
  permutation_upper _ _ _ [34,65,40,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3162

theorem m6138_68 : Upper (D 3) (R 3) [34,65,48,384,68] 13 :=
  permutation_upper _ _ _ [34,65,40,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3165

theorem m6138_72 : Upper (D 3) (R 3) [34,65,48,384,72] 13 :=
  permutation_upper _ _ _ [34,65,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3170

theorem m6138_129 : Upper (D 3) (R 3) [34,65,48,384,129] 13 :=
  permutation_upper _ _ _ [34,65,40,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3179

theorem m6138_132 : Upper (D 3) (R 3) [34,65,48,384,132] 13 :=
  permutation_upper _ _ _ [34,65,40,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3184

theorem m6138_136 : Upper (D 3) (R 3) [34,65,48,384,136] 13 :=
  permutation_upper _ _ _ [34,65,40,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3193

theorem m6138_192 : Upper (D 3) (R 3) [34,65,48,384,192] 13 :=
  permutation_upper _ _ _ [34,65,40,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3198

def r6138 : Route 9 := (fun mask => (mask,id))

def c6138 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6138 : Upper (D 3) (R 3) [34,65,48,384] 13 := by
  apply FastRouting.sound _ _ [34,65,48,384] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r6138 c6138
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6138_5
  · exact m6138_9
  · exact m6138_12
  · exact m6138_65
  · exact m6138_68
  · exact m6138_72
  · exact m6138_129
  · exact m6138_132
  · exact m6138_136
  · exact m6138_192

def b6139 : PairBound 9 := { available := 444, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 137 444 444 508 444 444), lower := (rows 35 67 69 137 16 32 64 128 256), losses := [] }

theorem u6139 : Upper (D 3) (R 3) [34,65,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6139
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6140 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 441 441 505 441 441), lower := (rows 35 67 69 140 16 32 64 128 256), losses := [] }

theorem u6140 : Upper (D 3) (R 3) [34,65,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6140
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6141 : PairBound 9 := { available := 413, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 168 413 445 477 413 413), lower := (rows 35 67 69 168 16 32 64 128 256), losses := [] }

theorem u6141 : Upper (D 3) (R 3) [34,65,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6141
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6142 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 265 188 188 252 188 444), lower := (rows 35 67 69 265 16 32 64 128 256), losses := [] }

theorem u6142 : Upper (D 3) (R 3) [34,65,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6142
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6143 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 268 185 185 249 185 441), lower := (rows 35 67 69 268 16 32 64 128 256), losses := [] }

theorem u6143 : Upper (D 3) (R 3) [34,65,65,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6143
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6144 : PairBound 9 := { available := 157, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 296 157 189 221 157 413), lower := (rows 35 67 69 296 16 32 64 128 256), losses := [] }

theorem u6144 : Upper (D 3) (R 3) [34,65,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6144
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6145 : PairBound 9 := { available := 189, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 392 189 189 253 189 445), lower := (rows 35 67 69 392 16 32 64 128 256), losses := [] }

theorem u6145 : Upper (D 3) (R 3) [34,65,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6145
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6146_5 : Upper (D 3) (R 3) [34,65,72,129,5] 13 :=
  permutation_upper _ _ _ [34,65,9,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2978

theorem m6146_33 : Upper (D 3) (R 3) [34,65,72,129,33] 13 :=
  permutation_upper _ _ _ [34,65,33,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3134

theorem m6146_36 : Upper (D 3) (R 3) [34,65,72,129,36] 13 :=
  permutation_upper _ _ _ [34,65,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3166

def r6146 : Route 9 := (fun mask => (mask,id))

def c6146 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6146 : Upper (D 3) (R 3) [34,65,72,129] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r6146 c6146
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6146_5
  · exact m6146_33
  · exact m6146_36
  · exact u3237
  · exact u3238
  · exact u3239
  · exact u3240
  · exact u3241
  · exact u3242
  · exact u3243

def b6147 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 140 433 433 497 433 433), lower := (rows 35 67 76 140 16 32 64 128 256), losses := [] }

theorem u6147 : Upper (D 3) (R 3) [34,65,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6147
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6148_5 : Upper (D 3) (R 3) [34,65,72,144,5] 13 :=
  permutation_upper _ _ _ [34,65,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2979

theorem m6148_33 : Upper (D 3) (R 3) [34,65,72,144,33] 13 :=
  permutation_upper _ _ _ [34,65,33,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3135

theorem m6148_36 : Upper (D 3) (R 3) [34,65,72,144,36] 13 :=
  permutation_upper _ _ _ [34,65,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3167

def r6148 : Route 9 := (fun mask => (mask,id))

def c6148 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6148 : Upper (D 3) (R 3) [34,65,72,144] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r6148 c6148
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6148_5
  · exact m6148_33
  · exact m6148_36
  · exact u3249
  · exact u3250
  · exact u3251
  · exact u3252
  · exact u3253
  · exact u3254
  · exact u3255

theorem m6149_5 : Upper (D 3) (R 3) [34,65,72,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2980

def r6149 : Route 9 := (fun mask => (mask,id))

def c6149 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6149 : Upper (D 3) (R 3) [34,65,72,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160] 13 (by decide) (choices 2) [5,129,132,257,260,384] r6149 c6149
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6149_5
  · exact u3256
  · exact u3257
  · exact u3258
  · exact u3259
  · exact u3260

theorem m6150_5 : Upper (D 3) (R 3) [34,65,72,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2981

theorem m6150_33 : Upper (D 3) (R 3) [34,65,72,257,33] 13 :=
  permutation_upper _ _ _ [34,65,33,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3136

theorem m6150_36 : Upper (D 3) (R 3) [34,65,72,257,36] 13 :=
  permutation_upper _ _ _ [34,65,40,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3168

def r6150 : Route 9 := (fun mask => (mask,id))

def c6150 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6150 : Upper (D 3) (R 3) [34,65,72,257] 13 := by
  apply FastRouting.sound _ _ [34,65,72,257] 13 (by decide) (choices 2) [5,33,36,129,132,160] r6150 c6150
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6150_5
  · exact m6150_33
  · exact m6150_36
  · exact u3261
  · exact u3262
  · exact u3263

def b6151 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 268 177 177 241 177 433), lower := (rows 35 67 76 268 16 32 64 128 256), losses := [] }

theorem u6151 : Upper (D 3) (R 3) [34,65,72,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6151
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6152_5 : Upper (D 3) (R 3) [34,65,72,272,5] 13 :=
  permutation_upper _ _ _ [34,65,9,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2982

theorem m6152_33 : Upper (D 3) (R 3) [34,65,72,272,33] 13 :=
  permutation_upper _ _ _ [34,65,33,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3137

theorem m6152_36 : Upper (D 3) (R 3) [34,65,72,272,36] 13 :=
  permutation_upper _ _ _ [34,65,40,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3169

def r6152 : Route 9 := (fun mask => (mask,id))

def c6152 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6152 : Upper (D 3) (R 3) [34,65,72,272] 13 := by
  apply FastRouting.sound _ _ [34,65,72,272] 13 (by decide) (choices 2) [5,33,36,129,132,160] r6152 c6152
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6152_5
  · exact m6152_33
  · exact m6152_36
  · exact u3266
  · exact u3267
  · exact u3268

theorem m6153_5 : Upper (D 3) (R 3) [34,65,72,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2983

def r6153 : Route 9 := (fun mask => (mask,id))

def c6153 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6153 : Upper (D 3) (R 3) [34,65,72,288] 13 := by
  apply FastRouting.sound _ _ [34,65,72,288] 13 (by decide) (choices 2) [5,129,132] r6153 c6153
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6153_5
  · exact u3269
  · exact u3270

theorem m6154_5 : Upper (D 3) (R 3) [34,65,72,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2984

theorem m6154_33 : Upper (D 3) (R 3) [34,65,72,384,33] 13 :=
  permutation_upper _ _ _ [34,65,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3138

theorem m6154_36 : Upper (D 3) (R 3) [34,65,72,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3170

def r6154 : Route 9 := (fun mask => (mask,id))

def c6154 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6154 : Upper (D 3) (R 3) [34,65,72,384] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384] 13 (by decide) (choices 2) [5,33,36,129,132,160] r6154 c6154
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6154_5
  · exact m6154_33
  · exact m6154_36
  · exact u3271
  · exact u3272
  · exact u3273

theorem m6155_5 : Upper (D 3) (R 3) [34,65,80,129,5] 13 :=
  permutation_upper _ _ _ [34,65,9,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2972

theorem m6155_9 : Upper (D 3) (R 3) [34,65,80,129,9] 13 :=
  permutation_upper _ _ _ [34,65,9,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2991

theorem m6155_12 : Upper (D 3) (R 3) [34,65,80,129,12] 13 :=
  permutation_upper _ _ _ [34,65,24,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3095

theorem m6155_33 : Upper (D 3) (R 3) [34,65,80,129,33] 13 :=
  permutation_upper _ _ _ [34,65,33,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3129

theorem m6155_36 : Upper (D 3) (R 3) [34,65,80,129,36] 13 :=
  permutation_upper _ _ _ [34,65,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3163

theorem m6155_40 : Upper (D 3) (R 3) [34,65,80,129,40] 13 :=
  permutation_upper _ _ _ [34,65,40,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3172

theorem m6155_129 : Upper (D 3) (R 3) [34,65,80,129,129] 13 :=
  permutation_upper _ _ _ [34,65,72,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3237

theorem m6155_132 : Upper (D 3) (R 3) [34,65,80,129,132] 13 :=
  permutation_upper _ _ _ [34,65,72,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3244

theorem m6155_136 : Upper (D 3) (R 3) [34,65,80,129,136] 13 :=
  permutation_upper _ _ _ [34,65,72,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3249

theorem m6155_160 : Upper (D 3) (R 3) [34,65,80,129,160] 13 :=
  permutation_upper _ _ _ [34,65,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3256

theorem m6155_257 : Upper (D 3) (R 3) [34,65,80,129,257] 13 :=
  permutation_upper _ _ _ [34,65,72,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3261

theorem m6155_260 : Upper (D 3) (R 3) [34,65,80,129,260] 13 :=
  permutation_upper _ _ _ [34,65,72,260,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3264

theorem m6155_264 : Upper (D 3) (R 3) [34,65,80,129,264] 13 :=
  permutation_upper _ _ _ [34,65,72,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3266

theorem m6155_288 : Upper (D 3) (R 3) [34,65,80,129,288] 13 :=
  permutation_upper _ _ _ [34,65,72,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3269

theorem m6155_384 : Upper (D 3) (R 3) [34,65,80,129,384] 13 :=
  permutation_upper _ _ _ [34,65,72,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3271

def r6155 : Route 9 := (fun mask => (mask,id))

def c6155 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6155 : Upper (D 3) (R 3) [34,65,80,129] 13 := by
  apply FastRouting.sound _ _ [34,65,80,129] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,257,260,264,288,384] r6155 c6155
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6155_5
  · exact m6155_9
  · exact m6155_12
  · exact m6155_33
  · exact m6155_36
  · exact m6155_40
  · exact m6155_129
  · exact m6155_132
  · exact m6155_136
  · exact m6155_160
  · exact m6155_257
  · exact m6155_260
  · exact m6155_264
  · exact m6155_288
  · exact m6155_384

theorem m6156_9 : Upper (D 3) (R 3) [34,65,80,132,9] 13 :=
  permutation_upper _ _ _ [34,65,9,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3012

theorem m6156_33 : Upper (D 3) (R 3) [34,65,80,132,33] 13 :=
  permutation_upper _ _ _ [34,65,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3130

theorem m6156_40 : Upper (D 3) (R 3) [34,65,80,132,40] 13 :=
  permutation_upper _ _ _ [34,65,40,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3186

theorem m6156_129 : Upper (D 3) (R 3) [34,65,80,132,129] 13 :=
  permutation_upper _ _ _ [34,65,72,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3238

theorem m6156_136 : Upper (D 3) (R 3) [34,65,80,132,136] 13 :=
  permutation_upper _ _ _ [34,65,72,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3250

theorem m6156_160 : Upper (D 3) (R 3) [34,65,80,132,160] 13 :=
  permutation_upper _ _ _ [34,65,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3257

theorem m6156_257 : Upper (D 3) (R 3) [34,65,80,132,257] 13 :=
  permutation_upper _ _ _ [34,65,72,257,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3262

theorem m6156_264 : Upper (D 3) (R 3) [34,65,80,132,264] 13 :=
  permutation_upper _ _ _ [34,65,72,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3267

theorem m6156_288 : Upper (D 3) (R 3) [34,65,80,132,288] 13 :=
  permutation_upper _ _ _ [34,65,72,288,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3270

theorem m6156_384 : Upper (D 3) (R 3) [34,65,80,132,384] 13 :=
  permutation_upper _ _ _ [34,65,72,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3272

def r6156 : Route 9 := (fun mask => (mask,id))

def c6156 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6156 : Upper (D 3) (R 3) [34,65,80,132] 13 := by
  apply FastRouting.sound _ _ [34,65,80,132] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r6156 c6156
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6156_9
  · exact m6156_33
  · exact m6156_40
  · exact m6156_129
  · exact m6156_136
  · exact m6156_160
  · exact m6156_257
  · exact m6156_264
  · exact m6156_288
  · exact m6156_384

theorem m6157_5 : Upper (D 3) (R 3) [34,65,80,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2973

theorem m6157_9 : Upper (D 3) (R 3) [34,65,80,160,9] 13 :=
  permutation_upper _ _ _ [34,65,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3023

theorem m6157_12 : Upper (D 3) (R 3) [34,65,80,160,12] 13 :=
  permutation_upper _ _ _ [34,65,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3096

theorem m6157_129 : Upper (D 3) (R 3) [34,65,80,160,129] 13 :=
  permutation_upper _ _ _ [34,65,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3239

theorem m6157_132 : Upper (D 3) (R 3) [34,65,80,160,132] 13 :=
  permutation_upper _ _ _ [34,65,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3245

theorem m6157_136 : Upper (D 3) (R 3) [34,65,80,160,136] 13 :=
  permutation_upper _ _ _ [34,65,72,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3251

theorem m6157_257 : Upper (D 3) (R 3) [34,65,80,160,257] 13 :=
  permutation_upper _ _ _ [34,65,72,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3263

theorem m6157_260 : Upper (D 3) (R 3) [34,65,80,160,260] 13 :=
  permutation_upper _ _ _ [34,65,72,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3265

theorem m6157_264 : Upper (D 3) (R 3) [34,65,80,160,264] 13 :=
  permutation_upper _ _ _ [34,65,72,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3268

theorem m6157_384 : Upper (D 3) (R 3) [34,65,80,160,384] 13 :=
  permutation_upper _ _ _ [34,65,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3273

def r6157 : Route 9 := (fun mask => (mask,id))

def c6157 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6157 : Upper (D 3) (R 3) [34,65,80,160] 13 := by
  apply FastRouting.sound _ _ [34,65,80,160] 13 (by decide) (choices 2) [5,9,12,129,132,136,257,260,264,384] r6157 c6157
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6157_5
  · exact m6157_9
  · exact m6157_12
  · exact m6157_129
  · exact m6157_132
  · exact m6157_136
  · exact m6157_257
  · exact m6157_260
  · exact m6157_264
  · exact m6157_384

theorem m6158_5 : Upper (D 3) (R 3) [34,65,80,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2974

theorem m6158_9 : Upper (D 3) (R 3) [34,65,80,257,9] 13 :=
  permutation_upper _ _ _ [34,65,9,257,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3040

theorem m6158_12 : Upper (D 3) (R 3) [34,65,80,257,12] 13 :=
  permutation_upper _ _ _ [34,65,24,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3097

theorem m6158_33 : Upper (D 3) (R 3) [34,65,80,257,33] 13 :=
  permutation_upper _ _ _ [34,65,33,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3131

theorem m6158_36 : Upper (D 3) (R 3) [34,65,80,257,36] 13 :=
  permutation_upper _ _ _ [34,65,40,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3164

theorem m6158_40 : Upper (D 3) (R 3) [34,65,80,257,40] 13 :=
  permutation_upper _ _ _ [34,65,40,257,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3200

theorem m6158_129 : Upper (D 3) (R 3) [34,65,80,257,129] 13 :=
  permutation_upper _ _ _ [34,65,72,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3240

theorem m6158_132 : Upper (D 3) (R 3) [34,65,80,257,132] 13 :=
  permutation_upper _ _ _ [34,65,72,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3246

theorem m6158_136 : Upper (D 3) (R 3) [34,65,80,257,136] 13 :=
  permutation_upper _ _ _ [34,65,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3252

theorem m6158_160 : Upper (D 3) (R 3) [34,65,80,257,160] 13 :=
  permutation_upper _ _ _ [34,65,72,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3258

def r6158 : Route 9 := (fun mask => (mask,id))

def c6158 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6158 : Upper (D 3) (R 3) [34,65,80,257] 13 := by
  apply FastRouting.sound _ _ [34,65,80,257] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r6158 c6158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6158_5
  · exact m6158_9
  · exact m6158_12
  · exact m6158_33
  · exact m6158_36
  · exact m6158_40
  · exact m6158_129
  · exact m6158_132
  · exact m6158_136
  · exact m6158_160

theorem m6159_9 : Upper (D 3) (R 3) [34,65,80,260,9] 13 :=
  permutation_upper _ _ _ [34,65,9,272,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3053

theorem m6159_33 : Upper (D 3) (R 3) [34,65,80,260,33] 13 :=
  permutation_upper _ _ _ [34,65,33,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3132

theorem m6159_40 : Upper (D 3) (R 3) [34,65,80,260,40] 13 :=
  permutation_upper _ _ _ [34,65,40,272,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3207

theorem m6159_129 : Upper (D 3) (R 3) [34,65,80,260,129] 13 :=
  permutation_upper _ _ _ [34,65,72,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3241

theorem m6159_136 : Upper (D 3) (R 3) [34,65,80,260,136] 13 :=
  permutation_upper _ _ _ [34,65,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3253

theorem m6159_160 : Upper (D 3) (R 3) [34,65,80,260,160] 13 :=
  permutation_upper _ _ _ [34,65,72,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3259

def r6159 : Route 9 := (fun mask => (mask,id))

def c6159 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6159 : Upper (D 3) (R 3) [34,65,80,260] 13 := by
  apply FastRouting.sound _ _ [34,65,80,260] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6159 c6159
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6159_9
  · exact m6159_33
  · exact m6159_40
  · exact m6159_129
  · exact m6159_136
  · exact m6159_160

theorem m6160_5 : Upper (D 3) (R 3) [34,65,80,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2975

theorem m6160_9 : Upper (D 3) (R 3) [34,65,80,288,9] 13 :=
  permutation_upper _ _ _ [34,65,9,288,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3059

theorem m6160_12 : Upper (D 3) (R 3) [34,65,80,288,12] 13 :=
  permutation_upper _ _ _ [34,65,24,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3098

theorem m6160_129 : Upper (D 3) (R 3) [34,65,80,288,129] 13 :=
  permutation_upper _ _ _ [34,65,72,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3242

theorem m6160_132 : Upper (D 3) (R 3) [34,65,80,288,132] 13 :=
  permutation_upper _ _ _ [34,65,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3247

theorem m6160_136 : Upper (D 3) (R 3) [34,65,80,288,136] 13 :=
  permutation_upper _ _ _ [34,65,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3254

def r6160 : Route 9 := (fun mask => (mask,id))

def c6160 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6160 : Upper (D 3) (R 3) [34,65,80,288] 13 := by
  apply FastRouting.sound _ _ [34,65,80,288] 13 (by decide) (choices 2) [5,9,12,129,132,136] r6160 c6160
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6160_5
  · exact m6160_9
  · exact m6160_12
  · exact m6160_129
  · exact m6160_132
  · exact m6160_136

theorem m6161_5 : Upper (D 3) (R 3) [34,65,80,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2976

theorem m6161_9 : Upper (D 3) (R 3) [34,65,80,384,9] 13 :=
  permutation_upper _ _ _ [34,65,9,384,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3070

theorem m6161_12 : Upper (D 3) (R 3) [34,65,80,384,12] 13 :=
  permutation_upper _ _ _ [34,65,24,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3099

theorem m6161_33 : Upper (D 3) (R 3) [34,65,80,384,33] 13 :=
  permutation_upper _ _ _ [34,65,33,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3133

theorem m6161_36 : Upper (D 3) (R 3) [34,65,80,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3165

theorem m6161_40 : Upper (D 3) (R 3) [34,65,80,384,40] 13 :=
  permutation_upper _ _ _ [34,65,40,384,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3214

theorem m6161_129 : Upper (D 3) (R 3) [34,65,80,384,129] 13 :=
  permutation_upper _ _ _ [34,65,72,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3243

theorem m6161_132 : Upper (D 3) (R 3) [34,65,80,384,132] 13 :=
  permutation_upper _ _ _ [34,65,72,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3248

theorem m6161_136 : Upper (D 3) (R 3) [34,65,80,384,136] 13 :=
  permutation_upper _ _ _ [34,65,72,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3255

theorem m6161_160 : Upper (D 3) (R 3) [34,65,80,384,160] 13 :=
  permutation_upper _ _ _ [34,65,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3260

def r6161 : Route 9 := (fun mask => (mask,id))

def c6161 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6161 : Upper (D 3) (R 3) [34,65,80,384] 13 := by
  apply FastRouting.sound _ _ [34,65,80,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r6161 c6161
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6161_5
  · exact m6161_9
  · exact m6161_12
  · exact m6161_33
  · exact m6161_36
  · exact m6161_40
  · exact m6161_129
  · exact m6161_132
  · exact m6161_136
  · exact m6161_160

def b6162 : PairBound 9 := { available := 413, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 137 413 445 477 413 413), lower := (rows 35 67 100 137 16 32 64 128 256), losses := [] }

theorem u6162 : Upper (D 3) (R 3) [34,65,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6162
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6163 : PairBound 9 := { available := 409, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 140 409 441 473 409 409), lower := (rows 35 67 100 140 16 32 64 128 256), losses := [] }

theorem u6163 : Upper (D 3) (R 3) [34,65,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6163
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6164 : PairBound 9 := { available := 157, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 265 157 189 221 157 413), lower := (rows 35 67 100 265 16 32 64 128 256), losses := [] }

theorem u6164 : Upper (D 3) (R 3) [34,65,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6164
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6165 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 268 153 185 217 153 409), lower := (rows 35 67 100 268 16 32 64 128 256), losses := [] }

theorem u6165 : Upper (D 3) (R 3) [34,65,96,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6165
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6166 : PairBound 9 := { available := 157, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 392 157 189 221 157 413), lower := (rows 35 67 100 392 16 32 64 128 256), losses := [] }

theorem u6166 : Upper (D 3) (R 3) [34,65,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6166
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6167 : PairBound 9 := { available := 380, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 133 137 380 380 380 508 380), lower := (rows 35 67 133 137 16 32 64 128 256), losses := [] }

theorem u6167 : Upper (D 3) (R 3) [34,65,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6167
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6168 : PairBound 9 := { available := 377, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 140 377 377 377 505 377), lower := (rows 35 67 133 140 16 32 64 128 256), losses := [] }

theorem u6168 : Upper (D 3) (R 3) [34,65,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6168
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6169_5 : Upper (D 3) (R 3) [34,65,129,144,5] 13 :=
  permutation_upper _ _ _ [34,65,9,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2992

theorem m6169_9 : Upper (D 3) (R 3) [34,65,129,144,9] 13 :=
  permutation_upper _ _ _ [34,65,9,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3002

theorem m6169_12 : Upper (D 3) (R 3) [34,65,129,144,12] 13 :=
  permutation_upper _ _ _ [34,65,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3106

theorem m6169_33 : Upper (D 3) (R 3) [34,65,129,144,33] 13 :=
  permutation_upper _ _ _ [34,65,33,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3139

theorem m6169_36 : Upper (D 3) (R 3) [34,65,129,144,36] 13 :=
  permutation_upper _ _ _ [34,65,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3174

theorem m6169_40 : Upper (D 3) (R 3) [34,65,129,144,40] 13 :=
  permutation_upper _ _ _ [34,65,40,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3180

theorem m6169_65 : Upper (D 3) (R 3) [34,65,129,144,65] 13 :=
  permutation_upper _ _ _ [34,65,65,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3218

theorem m6169_68 : Upper (D 3) (R 3) [34,65,129,144,68] 13 :=
  permutation_upper _ _ _ [34,65,72,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3238

theorem m6169_72 : Upper (D 3) (R 3) [34,65,129,144,72] 13 :=
  permutation_upper _ _ _ [34,65,72,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3244

theorem m6169_96 : Upper (D 3) (R 3) [34,65,129,144,96] 13 :=
  permutation_upper _ _ _ [34,65,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3274

def r6169 : Route 9 := (fun mask => (mask,id))

def c6169 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u6169 : Upper (D 3) (R 3) [34,65,129,144] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,257,260,264,288,320] r6169 c6169
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6169_5
  · exact m6169_9
  · exact m6169_12
  · exact m6169_33
  · exact m6169_36
  · exact m6169_40
  · exact m6169_65
  · exact m6169_68
  · exact m6169_72
  · exact m6169_96
  · exact u3292
  · exact u3293
  · exact u3294
  · exact u3295
  · exact u3296

theorem m6170_5 : Upper (D 3) (R 3) [34,65,129,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2993

theorem m6170_9 : Upper (D 3) (R 3) [34,65,129,160,9] 13 :=
  permutation_upper _ _ _ [34,65,9,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3024

theorem m6170_12 : Upper (D 3) (R 3) [34,65,129,160,12] 13 :=
  permutation_upper _ _ _ [34,65,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3107

theorem m6170_65 : Upper (D 3) (R 3) [34,65,129,160,65] 13 :=
  permutation_upper _ _ _ [34,65,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3219

theorem m6170_68 : Upper (D 3) (R 3) [34,65,129,160,68] 13 :=
  permutation_upper _ _ _ [34,65,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3239

theorem m6170_72 : Upper (D 3) (R 3) [34,65,129,160,72] 13 :=
  permutation_upper _ _ _ [34,65,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3256

def r6170 : Route 9 := (fun mask => (mask,id))

def c6170 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u6170 : Upper (D 3) (R 3) [34,65,129,160] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r6170 c6170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6170_5
  · exact m6170_9
  · exact m6170_12
  · exact m6170_65
  · exact m6170_68
  · exact m6170_72
  · exact u3297
  · exact u3298
  · exact u3299
  · exact u3300

theorem m6171_5 : Upper (D 3) (R 3) [34,65,129,192,5] 13 :=
  permutation_upper _ _ _ [34,65,9,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2994

theorem m6171_9 : Upper (D 3) (R 3) [34,65,129,192,9] 13 :=
  permutation_upper _ _ _ [34,65,9,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3032

theorem m6171_12 : Upper (D 3) (R 3) [34,65,129,192,12] 13 :=
  permutation_upper _ _ _ [34,65,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3108

theorem m6171_33 : Upper (D 3) (R 3) [34,65,129,192,33] 13 :=
  permutation_upper _ _ _ [34,65,33,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3140

theorem m6171_36 : Upper (D 3) (R 3) [34,65,129,192,36] 13 :=
  permutation_upper _ _ _ [34,65,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3175

theorem m6171_40 : Upper (D 3) (R 3) [34,65,129,192,40] 13 :=
  permutation_upper _ _ _ [34,65,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3194

def r6171 : Route 9 := (fun mask => (mask,id))

def c6171 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6171 : Upper (D 3) (R 3) [34,65,129,192] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r6171 c6171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6171_5
  · exact m6171_9
  · exact m6171_12
  · exact m6171_33
  · exact m6171_36
  · exact m6171_40
  · exact u3301
  · exact u3302
  · exact u3303
  · exact u3304

theorem m6172_12 : Upper (D 3) (R 3) [34,65,129,257,12] 13 :=
  permutation_upper _ _ _ [34,65,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3109

theorem m6172_36 : Upper (D 3) (R 3) [34,65,129,257,36] 13 :=
  permutation_upper _ _ _ [34,65,40,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3176

theorem m6172_40 : Upper (D 3) (R 3) [34,65,129,257,40] 13 :=
  permutation_upper _ _ _ [34,65,40,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3201

theorem m6172_68 : Upper (D 3) (R 3) [34,65,129,257,68] 13 :=
  permutation_upper _ _ _ [34,65,72,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3240

theorem m6172_72 : Upper (D 3) (R 3) [34,65,129,257,72] 13 :=
  permutation_upper _ _ _ [34,65,72,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3261

theorem m6172_96 : Upper (D 3) (R 3) [34,65,129,257,96] 13 :=
  permutation_upper _ _ _ [34,65,96,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3275

theorem m6172_132 : Upper (D 3) (R 3) [34,65,129,257,132] 13 :=
  permutation_upper _ _ _ [34,65,129,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3288

theorem m6172_136 : Upper (D 3) (R 3) [34,65,129,257,136] 13 :=
  permutation_upper _ _ _ [34,65,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3292

theorem m6172_160 : Upper (D 3) (R 3) [34,65,129,257,160] 13 :=
  permutation_upper _ _ _ [34,65,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3297

theorem m6172_192 : Upper (D 3) (R 3) [34,65,129,257,192] 13 :=
  permutation_upper _ _ _ [34,65,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3301

def r6172 : Route 9 := (fun mask => (mask,id))

def c6172 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6172 : Upper (D 3) (R 3) [34,65,129,257] 13 := by
  apply FastRouting.sound _ _ [34,65,129,257] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192] r6172 c6172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6172_12
  · exact m6172_36
  · exact m6172_40
  · exact m6172_68
  · exact m6172_72
  · exact m6172_96
  · exact m6172_132
  · exact m6172_136
  · exact m6172_160
  · exact m6172_192

theorem m6173_9 : Upper (D 3) (R 3) [34,65,129,260,9] 13 :=
  permutation_upper _ _ _ [34,65,9,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3055

theorem m6173_33 : Upper (D 3) (R 3) [34,65,129,260,33] 13 :=
  permutation_upper _ _ _ [34,65,33,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3142

theorem m6173_40 : Upper (D 3) (R 3) [34,65,129,260,40] 13 :=
  permutation_upper _ _ _ [34,65,40,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3208

theorem m6173_65 : Upper (D 3) (R 3) [34,65,129,260,65] 13 :=
  permutation_upper _ _ _ [34,65,65,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3221

theorem m6173_72 : Upper (D 3) (R 3) [34,65,129,260,72] 13 :=
  permutation_upper _ _ _ [34,65,72,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3266

theorem m6173_96 : Upper (D 3) (R 3) [34,65,129,260,96] 13 :=
  permutation_upper _ _ _ [34,65,96,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3277

theorem m6173_129 : Upper (D 3) (R 3) [34,65,129,260,129] 13 :=
  permutation_upper _ _ _ [34,65,129,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3285

theorem m6173_136 : Upper (D 3) (R 3) [34,65,129,260,136] 13 :=
  permutation_upper _ _ _ [34,65,129,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3293

theorem m6173_160 : Upper (D 3) (R 3) [34,65,129,260,160] 13 :=
  permutation_upper _ _ _ [34,65,129,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3298

theorem m6173_192 : Upper (D 3) (R 3) [34,65,129,260,192] 13 :=
  permutation_upper _ _ _ [34,65,129,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3302

def r6173 : Route 9 := (fun mask => (mask,id))

def c6173 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6173 : Upper (D 3) (R 3) [34,65,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6173 c6173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6173_9
  · exact m6173_33
  · exact m6173_40
  · exact m6173_65
  · exact m6173_72
  · exact m6173_96
  · exact m6173_129
  · exact m6173_136
  · exact m6173_160
  · exact m6173_192

theorem m6174_5 : Upper (D 3) (R 3) [34,65,129,272,5] 13 :=
  permutation_upper _ _ _ [34,65,9,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2995

theorem m6174_9 : Upper (D 3) (R 3) [34,65,129,272,9] 13 :=
  permutation_upper _ _ _ [34,65,9,260,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3047

theorem m6174_12 : Upper (D 3) (R 3) [34,65,129,272,12] 13 :=
  permutation_upper _ _ _ [34,65,24,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3110

theorem m6174_33 : Upper (D 3) (R 3) [34,65,129,272,33] 13 :=
  permutation_upper _ _ _ [34,65,33,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3141

theorem m6174_36 : Upper (D 3) (R 3) [34,65,129,272,36] 13 :=
  permutation_upper _ _ _ [34,65,40,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3177

theorem m6174_40 : Upper (D 3) (R 3) [34,65,129,272,40] 13 :=
  permutation_upper _ _ _ [34,65,40,260,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3204

theorem m6174_65 : Upper (D 3) (R 3) [34,65,129,272,65] 13 :=
  permutation_upper _ _ _ [34,65,65,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3220

theorem m6174_68 : Upper (D 3) (R 3) [34,65,129,272,68] 13 :=
  permutation_upper _ _ _ [34,65,72,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3241

theorem m6174_72 : Upper (D 3) (R 3) [34,65,129,272,72] 13 :=
  permutation_upper _ _ _ [34,65,72,260,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3264

theorem m6174_96 : Upper (D 3) (R 3) [34,65,129,272,96] 13 :=
  permutation_upper _ _ _ [34,65,96,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3276

theorem m6174_129 : Upper (D 3) (R 3) [34,65,129,272,129] 13 :=
  permutation_upper _ _ _ [34,65,129,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3285

theorem m6174_132 : Upper (D 3) (R 3) [34,65,129,272,132] 13 :=
  permutation_upper _ _ _ [34,65,129,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3289

theorem m6174_136 : Upper (D 3) (R 3) [34,65,129,272,136] 13 :=
  permutation_upper _ _ _ [34,65,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3294

theorem m6174_160 : Upper (D 3) (R 3) [34,65,129,272,160] 13 :=
  permutation_upper _ _ _ [34,65,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3299

theorem m6174_192 : Upper (D 3) (R 3) [34,65,129,272,192] 13 :=
  permutation_upper _ _ _ [34,65,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3303

def r6174 : Route 9 := (fun mask => (mask,id))

def c6174 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6174 : Upper (D 3) (R 3) [34,65,129,272] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r6174 c6174
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6174_5
  · exact m6174_9
  · exact m6174_12
  · exact m6174_33
  · exact m6174_36
  · exact m6174_40
  · exact m6174_65
  · exact m6174_68
  · exact m6174_72
  · exact m6174_96
  · exact m6174_129
  · exact m6174_132
  · exact m6174_136
  · exact m6174_160
  · exact m6174_192

theorem m6175_5 : Upper (D 3) (R 3) [34,65,129,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2996

theorem m6175_9 : Upper (D 3) (R 3) [34,65,129,288,9] 13 :=
  permutation_upper _ _ _ [34,65,9,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3060

theorem m6175_12 : Upper (D 3) (R 3) [34,65,129,288,12] 13 :=
  permutation_upper _ _ _ [34,65,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3111

theorem m6175_65 : Upper (D 3) (R 3) [34,65,129,288,65] 13 :=
  permutation_upper _ _ _ [34,65,65,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3222

theorem m6175_68 : Upper (D 3) (R 3) [34,65,129,288,68] 13 :=
  permutation_upper _ _ _ [34,65,72,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3242

theorem m6175_72 : Upper (D 3) (R 3) [34,65,129,288,72] 13 :=
  permutation_upper _ _ _ [34,65,72,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3269

theorem m6175_129 : Upper (D 3) (R 3) [34,65,129,288,129] 13 :=
  permutation_upper _ _ _ [34,65,129,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3286

theorem m6175_132 : Upper (D 3) (R 3) [34,65,129,288,132] 13 :=
  permutation_upper _ _ _ [34,65,129,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3290

theorem m6175_136 : Upper (D 3) (R 3) [34,65,129,288,136] 13 :=
  permutation_upper _ _ _ [34,65,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3295

theorem m6175_192 : Upper (D 3) (R 3) [34,65,129,288,192] 13 :=
  permutation_upper _ _ _ [34,65,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3304

def r6175 : Route 9 := (fun mask => (mask,id))

def c6175 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6175 : Upper (D 3) (R 3) [34,65,129,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r6175 c6175
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6175_5
  · exact m6175_9
  · exact m6175_12
  · exact m6175_65
  · exact m6175_68
  · exact m6175_72
  · exact m6175_129
  · exact m6175_132
  · exact m6175_136
  · exact m6175_192

theorem m6176_5 : Upper (D 3) (R 3) [34,65,129,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2997

theorem m6176_9 : Upper (D 3) (R 3) [34,65,129,320,9] 13 :=
  permutation_upper _ _ _ [34,65,9,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3064

theorem m6176_12 : Upper (D 3) (R 3) [34,65,129,320,12] 13 :=
  permutation_upper _ _ _ [34,65,24,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3112

theorem m6176_33 : Upper (D 3) (R 3) [34,65,129,320,33] 13 :=
  permutation_upper _ _ _ [34,65,33,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3143

theorem m6176_36 : Upper (D 3) (R 3) [34,65,129,320,36] 13 :=
  permutation_upper _ _ _ [34,65,40,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3178

theorem m6176_40 : Upper (D 3) (R 3) [34,65,129,320,40] 13 :=
  permutation_upper _ _ _ [34,65,40,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3211

theorem m6176_129 : Upper (D 3) (R 3) [34,65,129,320,129] 13 :=
  permutation_upper _ _ _ [34,65,129,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3287

theorem m6176_132 : Upper (D 3) (R 3) [34,65,129,320,132] 13 :=
  permutation_upper _ _ _ [34,65,129,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3291

theorem m6176_136 : Upper (D 3) (R 3) [34,65,129,320,136] 13 :=
  permutation_upper _ _ _ [34,65,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3296

theorem m6176_160 : Upper (D 3) (R 3) [34,65,129,320,160] 13 :=
  permutation_upper _ _ _ [34,65,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3300

def r6176 : Route 9 := (fun mask => (mask,id))

def c6176 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6176 : Upper (D 3) (R 3) [34,65,129,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r6176 c6176
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6176_5
  · exact m6176_9
  · exact m6176_12
  · exact m6176_33
  · exact m6176_36
  · exact m6176_40
  · exact m6176_129
  · exact m6176_132
  · exact m6176_136
  · exact m6176_160

theorem m6177_5 : Upper (D 3) (R 3) [34,65,129,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2998

theorem m6177_9 : Upper (D 3) (R 3) [34,65,129,384,9] 13 :=
  permutation_upper _ _ _ [34,65,9,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3072

theorem m6177_12 : Upper (D 3) (R 3) [34,65,129,384,12] 13 :=
  permutation_upper _ _ _ [34,65,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3113

theorem m6177_33 : Upper (D 3) (R 3) [34,65,129,384,33] 13 :=
  permutation_upper _ _ _ [34,65,33,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3144

theorem m6177_36 : Upper (D 3) (R 3) [34,65,129,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3179

theorem m6177_40 : Upper (D 3) (R 3) [34,65,129,384,40] 13 :=
  permutation_upper _ _ _ [34,65,40,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3215

theorem m6177_65 : Upper (D 3) (R 3) [34,65,129,384,65] 13 :=
  permutation_upper _ _ _ [34,65,65,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3223

theorem m6177_68 : Upper (D 3) (R 3) [34,65,129,384,68] 13 :=
  permutation_upper _ _ _ [34,65,72,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3243

theorem m6177_72 : Upper (D 3) (R 3) [34,65,129,384,72] 13 :=
  permutation_upper _ _ _ [34,65,72,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3271

theorem m6177_96 : Upper (D 3) (R 3) [34,65,129,384,96] 13 :=
  permutation_upper _ _ _ [34,65,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3278

def r6177 : Route 9 := (fun mask => (mask,id))

def c6177 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6177 : Upper (D 3) (R 3) [34,65,129,384] 13 := by
  apply FastRouting.sound _ _ [34,65,129,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r6177 c6177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6177_5
  · exact m6177_9
  · exact m6177_12
  · exact m6177_33
  · exact m6177_36
  · exact m6177_40
  · exact m6177_65
  · exact m6177_68
  · exact m6177_72
  · exact m6177_96

def b6178 : PairBound 9 := { available := 369, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 140 140 369 369 369 497 369), lower := (rows 35 67 140 140 16 32 64 128 256), losses := [] }

theorem u6178 : Upper (D 3) (R 3) [34,65,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6178
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6179 : PairBound 9 := { available := 357, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 152 373 357 357 485 357), lower := (rows 35 67 140 152 16 32 64 128 256), losses := [] }

theorem u6179 : Upper (D 3) (R 3) [34,65,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6179
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u6179
end Delivery.IrregularNine14.P03
