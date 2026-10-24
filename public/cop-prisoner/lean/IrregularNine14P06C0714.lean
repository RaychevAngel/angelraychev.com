import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0619
import IrregularNine14P06C0620
import IrregularNine14P06C0621
import IrregularNine14P06C0622
import IrregularNine14P06C0623

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b42840 : PairBound 9 := { available := 309, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 76 74 309 309 373 437 309), lower := (rows 35 131 76 74 16 32 64 128 256), losses := [] }

theorem u42840 : Upper (D 6) (R 6) [34,129,72,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42841 : PairBound 9 := { available := 311, camps := [{ cop := 6, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 76 311 311 375 439 311), lower := (rows 35 131 76 76 16 32 64 128 256), losses := [] }

theorem u42841 : Upper (D 6) (R 6) [34,129,72,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42842 : PairBound 9 := { available := 295, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 76 88 311 295 359 423 295), lower := (rows 35 131 76 88 16 32 64 128 256), losses := [] }

theorem u42842 : Upper (D 6) (R 6) [34,129,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42843 : PairBound 9 := { available := 279, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 76 104 279 311 343 407 279), lower := (rows 35 131 76 104 16 32 64 128 256), losses := [] }

theorem u42843 : Upper (D 6) (R 6) [34,129,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42844 : Route 9 := (fun mask => (mask,id))

def c42844 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42844 : Upper (D 6) (R 6) [34,129,72,257] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42844 c42844
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37168
  · exact u37169
  · exact u37170
  · exact u37171
  · exact u37172
  · exact u37173

def r42845 : Route 9 := (fun mask => (mask,id))

def c42845 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42845 : Upper (D 6) (R 6) [34,129,72,258] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42845 c42845
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37174
  · exact u37175
  · exact u37176
  · exact u37177
  · exact u37178
  · exact u37179

def r42846 : Route 9 := (fun mask => (mask,id))

def c42846 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42846 : Upper (D 6) (R 6) [34,129,72,260] 13 := by
  apply FastRouting.sound _ _ [34,129,72,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42846 c42846
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37180
  · exact u37181
  · exact u37182
  · exact u37183
  · exact u37184
  · exact u37185
  · exact u37186
  · exact u37187
  · exact u37188
  · exact u37189

def r42847 : Route 9 := (fun mask => (mask,id))

def c42847 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42847 : Upper (D 6) (R 6) [34,129,72,272] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42847 c42847
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37190
  · exact u37191
  · exact u37192
  · exact u37193
  · exact u37194
  · exact u37195
  · exact u37196
  · exact u37197
  · exact u37198
  · exact u37199

def r42848 : Route 9 := (fun mask => (mask,id))

def c42848 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42848 : Upper (D 6) (R 6) [34,129,72,288] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42848 c42848
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37200
  · exact u37201
  · exact u37202
  · exact u37203
  · exact u37204
  · exact u37205

def b42849 : PairBound 9 := { available := 55, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 76 328 55 55 119 183 311), lower := (rows 35 131 76 328 16 32 64 128 256), losses := [] }

theorem u42849 : Upper (D 6) (R 6) [34,129,72,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42850 : PairBound 9 := { available := 348, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 11 348 380 348 476 348), lower := (rows 35 131 100 11 16 32 64 128 256), losses := [] }

theorem u42850 : Upper (D 6) (R 6) [34,129,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42851 : Route 9 := (fun mask => (mask,id))

def c42851 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42851 : Upper (D 6) (R 6) [34,129,96,5] 13 := by
  apply FastRouting.sound _ _ [34,129,96,5] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r42851 c42851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37211
  · exact u37212
  · exact u37213
  · exact u37214
  · exact u37215
  · exact u37216
  · exact u37217
  · exact u37218
  · exact u37219
  · exact u37220

theorem m42852_5 : Upper (D 6) (R 6) [34,129,96,6,5] 13 :=
  permutation_upper _ _ _ [34,129,96,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37211

def r42852 : Route 9 := (fun mask => (mask,id))

def c42852 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42852 : Upper (D 6) (R 6) [34,129,96,6] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r42852 c42852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42852_5
  · exact u37221
  · exact u37222
  · exact u37223
  · exact u37224
  · exact u37225
  · exact u37226
  · exact u37227
  · exact u37228
  · exact u37229

theorem m42853_6 : Upper (D 6) (R 6) [34,129,96,17,6] 13 :=
  permutation_upper _ _ _ [34,129,96,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37221

def r42853 : Route 9 := (fun mask => (mask,id))

def c42853 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42853 : Upper (D 6) (R 6) [34,129,96,17] 13 := by
  apply FastRouting.sound _ _ [34,129,96,17] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r42853 c42853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42853_6
  · exact u37230
  · exact u37231
  · exact u37232
  · exact u37233
  · exact u37234
  · exact u37235
  · exact u37236
  · exact u37237
  · exact u37238

theorem m42854_5 : Upper (D 6) (R 6) [34,129,96,18,5] 13 :=
  permutation_upper _ _ _ [34,129,96,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37212

theorem m42854_9 : Upper (D 6) (R 6) [34,129,96,18,9] 13 :=
  permutation_upper _ _ _ [34,129,96,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37230

def r42854 : Route 9 := (fun mask => (mask,id))

def c42854 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42854 : Upper (D 6) (R 6) [34,129,96,18] 13 := by
  apply FastRouting.sound _ _ [34,129,96,18] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r42854 c42854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42854_5
  · exact m42854_9
  · exact u37239
  · exact u37240
  · exact u37241
  · exact u37242
  · exact u37243
  · exact u37244
  · exact u37245
  · exact u37246

theorem m42855_3 : Upper (D 6) (R 6) [34,129,96,20,3] 13 :=
  permutation_upper _ _ _ [34,129,96,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37206

theorem m42855_5 : Upper (D 6) (R 6) [34,129,96,20,5] 13 :=
  permutation_upper _ _ _ [34,129,96,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37213

theorem m42855_6 : Upper (D 6) (R 6) [34,129,96,20,6] 13 :=
  permutation_upper _ _ _ [34,129,96,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37222

theorem m42855_9 : Upper (D 6) (R 6) [34,129,96,20,9] 13 :=
  permutation_upper _ _ _ [34,129,96,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37231

theorem m42855_10 : Upper (D 6) (R 6) [34,129,96,20,10] 13 :=
  permutation_upper _ _ _ [34,129,96,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37239

def r42855 : Route 9 := (fun mask => (mask,id))

def c42855 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42855 : Upper (D 6) (R 6) [34,129,96,20] 13 := by
  apply FastRouting.sound _ _ [34,129,96,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,257,258,260,264,320] r42855 c42855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42855_3
  · exact m42855_5
  · exact m42855_6
  · exact m42855_9
  · exact m42855_10
  · exact u37247
  · exact u37248
  · exact u37249
  · exact u37250
  · exact u37251
  · exact u37252
  · exact u37253
  · exact u37254
  · exact u37255
  · exact u37256

theorem m42856_6 : Upper (D 6) (R 6) [34,129,96,65,6] 13 :=
  permutation_upper _ _ _ [34,129,96,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37223

theorem m42856_10 : Upper (D 6) (R 6) [34,129,96,65,10] 13 :=
  permutation_upper _ _ _ [34,129,96,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37240

theorem m42856_12 : Upper (D 6) (R 6) [34,129,96,65,12] 13 :=
  permutation_upper _ _ _ [34,129,96,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37248

def r42856 : Route 9 := (fun mask => (mask,id))

def c42856 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42856 : Upper (D 6) (R 6) [34,129,96,65] 13 := by
  apply FastRouting.sound _ _ [34,129,96,65] 13 (by decide) (choices 2) [6,10,12,258,260,264] r42856 c42856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42856_6
  · exact m42856_10
  · exact m42856_12
  · exact u37257
  · exact u37258
  · exact u37259

theorem m42857_5 : Upper (D 6) (R 6) [34,129,96,66,5] 13 :=
  permutation_upper _ _ _ [34,129,96,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37214

theorem m42857_9 : Upper (D 6) (R 6) [34,129,96,66,9] 13 :=
  permutation_upper _ _ _ [34,129,96,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37232

theorem m42857_12 : Upper (D 6) (R 6) [34,129,96,66,12] 13 :=
  permutation_upper _ _ _ [34,129,96,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37249

def r42857 : Route 9 := (fun mask => (mask,id))

def c42857 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42857 : Upper (D 6) (R 6) [34,129,96,66] 13 := by
  apply FastRouting.sound _ _ [34,129,96,66] 13 (by decide) (choices 2) [5,9,12,257,260,264] r42857 c42857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42857_5
  · exact m42857_9
  · exact m42857_12
  · exact u37260
  · exact u37261
  · exact u37262

def b42858 : PairBound 9 := { available := 287, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 100 76 287 319 351 415 287), lower := (rows 35 131 100 76 16 32 64 128 256), losses := [] }

theorem u42858 : Upper (D 6) (R 6) [34,129,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42859_3 : Upper (D 6) (R 6) [34,129,96,80,3] 13 :=
  permutation_upper _ _ _ [34,129,96,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37207

theorem m42859_5 : Upper (D 6) (R 6) [34,129,96,80,5] 13 :=
  permutation_upper _ _ _ [34,129,96,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37216

theorem m42859_6 : Upper (D 6) (R 6) [34,129,96,80,6] 13 :=
  permutation_upper _ _ _ [34,129,96,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37225

theorem m42859_9 : Upper (D 6) (R 6) [34,129,96,80,9] 13 :=
  permutation_upper _ _ _ [34,129,96,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37234

theorem m42859_10 : Upper (D 6) (R 6) [34,129,96,80,10] 13 :=
  permutation_upper _ _ _ [34,129,96,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37242

theorem m42859_12 : Upper (D 6) (R 6) [34,129,96,80,12] 13 :=
  permutation_upper _ _ _ [34,129,96,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37251

def r42859 : Route 9 := (fun mask => (mask,id))

def c42859 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42859 : Upper (D 6) (R 6) [34,129,96,80] 13 := by
  apply FastRouting.sound _ _ [34,129,96,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r42859 c42859
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42859_3
  · exact m42859_5
  · exact m42859_6
  · exact m42859_9
  · exact m42859_10
  · exact m42859_12
  · exact u37267
  · exact u37268
  · exact u37269
  · exact u37270

theorem m42860_6 : Upper (D 6) (R 6) [34,129,96,257,6] 13 :=
  permutation_upper _ _ _ [34,129,96,6,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37226

theorem m42860_10 : Upper (D 6) (R 6) [34,129,96,257,10] 13 :=
  permutation_upper _ _ _ [34,129,96,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37243

theorem m42860_12 : Upper (D 6) (R 6) [34,129,96,257,12] 13 :=
  permutation_upper _ _ _ [34,129,96,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37252

theorem m42860_66 : Upper (D 6) (R 6) [34,129,96,257,66] 13 :=
  permutation_upper _ _ _ [34,129,96,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37260

theorem m42860_68 : Upper (D 6) (R 6) [34,129,96,257,68] 13 :=
  permutation_upper _ _ _ [34,129,96,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37263

theorem m42860_72 : Upper (D 6) (R 6) [34,129,96,257,72] 13 :=
  permutation_upper _ _ _ [34,129,96,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37267

def r42860 : Route 9 := (fun mask => (mask,id))

def c42860 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42860 : Upper (D 6) (R 6) [34,129,96,257] 13 := by
  apply FastRouting.sound _ _ [34,129,96,257] 13 (by decide) (choices 2) [6,10,12,66,68,72] r42860 c42860
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42860_6
  · exact m42860_10
  · exact m42860_12
  · exact m42860_66
  · exact m42860_68
  · exact m42860_72

theorem m42861_5 : Upper (D 6) (R 6) [34,129,96,258,5] 13 :=
  permutation_upper _ _ _ [34,129,96,5,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37217

theorem m42861_9 : Upper (D 6) (R 6) [34,129,96,258,9] 13 :=
  permutation_upper _ _ _ [34,129,96,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37235

theorem m42861_12 : Upper (D 6) (R 6) [34,129,96,258,12] 13 :=
  permutation_upper _ _ _ [34,129,96,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37253

theorem m42861_65 : Upper (D 6) (R 6) [34,129,96,258,65] 13 :=
  permutation_upper _ _ _ [34,129,96,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37257

theorem m42861_68 : Upper (D 6) (R 6) [34,129,96,258,68] 13 :=
  permutation_upper _ _ _ [34,129,96,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37264

theorem m42861_72 : Upper (D 6) (R 6) [34,129,96,258,72] 13 :=
  permutation_upper _ _ _ [34,129,96,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37268

def r42861 : Route 9 := (fun mask => (mask,id))

def c42861 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42861 : Upper (D 6) (R 6) [34,129,96,258] 13 := by
  apply FastRouting.sound _ _ [34,129,96,258] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42861 c42861
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42861_5
  · exact m42861_9
  · exact m42861_12
  · exact m42861_65
  · exact m42861_68
  · exact m42861_72

theorem m42862_3 : Upper (D 6) (R 6) [34,129,96,260,3] 13 :=
  permutation_upper _ _ _ [34,129,96,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37208

theorem m42862_5 : Upper (D 6) (R 6) [34,129,96,260,5] 13 :=
  permutation_upper _ _ _ [34,129,96,5,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37218

theorem m42862_6 : Upper (D 6) (R 6) [34,129,96,260,6] 13 :=
  permutation_upper _ _ _ [34,129,96,6,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37227

theorem m42862_9 : Upper (D 6) (R 6) [34,129,96,260,9] 13 :=
  permutation_upper _ _ _ [34,129,96,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37236

theorem m42862_10 : Upper (D 6) (R 6) [34,129,96,260,10] 13 :=
  permutation_upper _ _ _ [34,129,96,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37244

theorem m42862_12 : Upper (D 6) (R 6) [34,129,96,260,12] 13 :=
  permutation_upper _ _ _ [34,129,96,20,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37254

theorem m42862_65 : Upper (D 6) (R 6) [34,129,96,260,65] 13 :=
  permutation_upper _ _ _ [34,129,96,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37258

theorem m42862_66 : Upper (D 6) (R 6) [34,129,96,260,66] 13 :=
  permutation_upper _ _ _ [34,129,96,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37261

theorem m42862_68 : Upper (D 6) (R 6) [34,129,96,260,68] 13 :=
  permutation_upper _ _ _ [34,129,96,68,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37265

theorem m42862_72 : Upper (D 6) (R 6) [34,129,96,260,72] 13 :=
  permutation_upper _ _ _ [34,129,96,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37269

def r42862 : Route 9 := (fun mask => (mask,id))

def c42862 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42862 : Upper (D 6) (R 6) [34,129,96,260] 13 := by
  apply FastRouting.sound _ _ [34,129,96,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42862 c42862
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42862_3
  · exact m42862_5
  · exact m42862_6
  · exact m42862_9
  · exact m42862_10
  · exact m42862_12
  · exact m42862_65
  · exact m42862_66
  · exact m42862_68
  · exact m42862_72

theorem m42863_3 : Upper (D 6) (R 6) [34,129,96,272,3] 13 :=
  permutation_upper _ _ _ [34,129,96,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37209

theorem m42863_5 : Upper (D 6) (R 6) [34,129,96,272,5] 13 :=
  permutation_upper _ _ _ [34,129,96,5,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37219

theorem m42863_6 : Upper (D 6) (R 6) [34,129,96,272,6] 13 :=
  permutation_upper _ _ _ [34,129,96,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37228

theorem m42863_9 : Upper (D 6) (R 6) [34,129,96,272,9] 13 :=
  permutation_upper _ _ _ [34,129,96,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37237

theorem m42863_10 : Upper (D 6) (R 6) [34,129,96,272,10] 13 :=
  permutation_upper _ _ _ [34,129,96,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37245

theorem m42863_12 : Upper (D 6) (R 6) [34,129,96,272,12] 13 :=
  permutation_upper _ _ _ [34,129,96,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37255

theorem m42863_65 : Upper (D 6) (R 6) [34,129,96,272,65] 13 :=
  permutation_upper _ _ _ [34,129,96,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37259

theorem m42863_66 : Upper (D 6) (R 6) [34,129,96,272,66] 13 :=
  permutation_upper _ _ _ [34,129,96,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37262

theorem m42863_68 : Upper (D 6) (R 6) [34,129,96,272,68] 13 :=
  permutation_upper _ _ _ [34,129,96,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37266

theorem m42863_72 : Upper (D 6) (R 6) [34,129,96,272,72] 13 :=
  permutation_upper _ _ _ [34,129,96,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37270

def r42863 : Route 9 := (fun mask => (mask,id))

def c42863 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42863 : Upper (D 6) (R 6) [34,129,96,272] 13 := by
  apply FastRouting.sound _ _ [34,129,96,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42863 c42863
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42863_3
  · exact m42863_5
  · exact m42863_6
  · exact m42863_9
  · exact m42863_10
  · exact m42863_12
  · exact m42863_65
  · exact m42863_66
  · exact m42863_68
  · exact m42863_72

theorem m42864_3 : Upper (D 6) (R 6) [34,129,96,320,3] 13 :=
  permutation_upper _ _ _ [34,129,96,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37210

theorem m42864_5 : Upper (D 6) (R 6) [34,129,96,320,5] 13 :=
  permutation_upper _ _ _ [34,129,96,5,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37220

theorem m42864_6 : Upper (D 6) (R 6) [34,129,96,320,6] 13 :=
  permutation_upper _ _ _ [34,129,96,6,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37229

theorem m42864_9 : Upper (D 6) (R 6) [34,129,96,320,9] 13 :=
  permutation_upper _ _ _ [34,129,96,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37238

theorem m42864_10 : Upper (D 6) (R 6) [34,129,96,320,10] 13 :=
  permutation_upper _ _ _ [34,129,96,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37246

theorem m42864_12 : Upper (D 6) (R 6) [34,129,96,320,12] 13 :=
  permutation_upper _ _ _ [34,129,96,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37256

def r42864 : Route 9 := (fun mask => (mask,id))

def c42864 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42864 : Upper (D 6) (R 6) [34,129,96,320] 13 := by
  apply FastRouting.sound _ _ [34,129,96,320] 13 (by decide) (choices 2) [3,5,6,9,10,12] r42864 c42864
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42864_3
  · exact m42864_5
  · exact m42864_6
  · exact m42864_9
  · exact m42864_10
  · exact m42864_12

def r42865 : Route 9 := (fun mask => (mask,id))

def c42865 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42865 : Upper (D 6) (R 6) [34,129,257,6] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6] 13 (by decide) (choices 2) [12,36,40,68,72,96] r42865 c42865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37271
  · exact u37272
  · exact u37273
  · exact u37274
  · exact u37275
  · exact u37276

def r42866 : Route 9 := (fun mask => (mask,id))

def c42866 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42866 : Upper (D 6) (R 6) [34,129,257,18] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18] 13 (by decide) (choices 2) [12,36,40,68,72,96] r42866 c42866
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37277
  · exact u37278
  · exact u37279
  · exact u37280
  · exact u37281
  · exact u37282

theorem m42867_6 : Upper (D 6) (R 6) [34,129,257,20,6] 13 :=
  permutation_upper _ _ _ [34,129,257,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37271

theorem m42867_10 : Upper (D 6) (R 6) [34,129,257,20,10] 13 :=
  permutation_upper _ _ _ [34,129,257,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37277

def r42867 : Route 9 := (fun mask => (mask,id))

def c42867 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42867 : Upper (D 6) (R 6) [34,129,257,20] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42867 c42867
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42867_6
  · exact m42867_10
  · exact u37283
  · exact u37284
  · exact u37285
  · exact u37286
  · exact u37287
  · exact u37288
  · exact u37289
  · exact u37290

def b42868 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 131 261 42 92 124 92 220 348), lower := (rows 35 131 261 42 16 32 64 128 256), losses := [] }

theorem u42868 : Upper (D 6) (R 6) [34,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42869_6 : Upper (D 6) (R 6) [34,129,257,36,6] 13 :=
  permutation_upper _ _ _ [34,129,257,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37272

theorem m42869_10 : Upper (D 6) (R 6) [34,129,257,36,10] 13 :=
  permutation_upper _ _ _ [34,129,257,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37278

theorem m42869_12 : Upper (D 6) (R 6) [34,129,257,36,12] 13 :=
  permutation_upper _ _ _ [34,129,257,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37285

def r42869 : Route 9 := (fun mask => (mask,id))

def c42869 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42869 : Upper (D 6) (R 6) [34,129,257,36] 13 := by
  apply FastRouting.sound _ _ [34,129,257,36] 13 (by decide) (choices 2) [6,10,12,66,68,72] r42869 c42869
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42869_6
  · exact m42869_10
  · exact m42869_12
  · exact u37293
  · exact u37294
  · exact u37295

theorem m42870_6 : Upper (D 6) (R 6) [34,129,257,48,6] 13 :=
  permutation_upper _ _ _ [34,129,257,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37273

theorem m42870_10 : Upper (D 6) (R 6) [34,129,257,48,10] 13 :=
  permutation_upper _ _ _ [34,129,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37279

theorem m42870_12 : Upper (D 6) (R 6) [34,129,257,48,12] 13 :=
  permutation_upper _ _ _ [34,129,257,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37286

def r42870 : Route 9 := (fun mask => (mask,id))

def c42870 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42870 : Upper (D 6) (R 6) [34,129,257,48] 13 := by
  apply FastRouting.sound _ _ [34,129,257,48] 13 (by decide) (choices 2) [6,10,12,66,68,72] r42870 c42870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42870_6
  · exact m42870_10
  · exact m42870_12
  · exact u37296
  · exact u37297
  · exact u37298

theorem m42871_12 : Upper (D 6) (R 6) [34,129,257,66,12] 13 :=
  permutation_upper _ _ _ [34,129,257,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37287

theorem m42871_36 : Upper (D 6) (R 6) [34,129,257,66,36] 13 :=
  permutation_upper _ _ _ [34,129,257,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37293

theorem m42871_40 : Upper (D 6) (R 6) [34,129,257,66,40] 13 :=
  permutation_upper _ _ _ [34,129,257,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37296

def r42871 : Route 9 := (fun mask => (mask,id))

def c42871 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42871 : Upper (D 6) (R 6) [34,129,257,66] 13 := by
  apply FastRouting.sound _ _ [34,129,257,66] 13 (by decide) (choices 2) [12,36,40,68,72,96] r42871 c42871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42871_12
  · exact m42871_36
  · exact m42871_40
  · exact u37299
  · exact u37300
  · exact u37301

theorem m42872_6 : Upper (D 6) (R 6) [34,129,257,68,6] 13 :=
  permutation_upper _ _ _ [34,129,257,6,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37274

theorem m42872_10 : Upper (D 6) (R 6) [34,129,257,68,10] 13 :=
  permutation_upper _ _ _ [34,129,257,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37280

theorem m42872_12 : Upper (D 6) (R 6) [34,129,257,68,12] 13 :=
  permutation_upper _ _ _ [34,129,257,20,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37288

theorem m42872_34 : Upper (D 6) (R 6) [34,129,257,68,34] 13 :=
  permutation_upper _ _ _ [34,129,257,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37291

theorem m42872_36 : Upper (D 6) (R 6) [34,129,257,68,36] 13 :=
  permutation_upper _ _ _ [34,129,257,36,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37294

theorem m42872_40 : Upper (D 6) (R 6) [34,129,257,68,40] 13 :=
  permutation_upper _ _ _ [34,129,257,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37297

theorem m42872_66 : Upper (D 6) (R 6) [34,129,257,68,66] 13 :=
  permutation_upper _ _ _ [34,129,257,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37299

def r42872 : Route 9 := (fun mask => (mask,id))

def c42872 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42872 : Upper (D 6) (R 6) [34,129,257,68] 13 := by
  apply FastRouting.sound _ _ [34,129,257,68] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42872 c42872
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42872_6
  · exact m42872_10
  · exact m42872_12
  · exact m42872_34
  · exact m42872_36
  · exact m42872_40
  · exact m42872_66
  · exact u37302
  · exact u37303
  · exact u37304

theorem m42873_6 : Upper (D 6) (R 6) [34,129,257,80,6] 13 :=
  permutation_upper _ _ _ [34,129,257,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37275

theorem m42873_10 : Upper (D 6) (R 6) [34,129,257,80,10] 13 :=
  permutation_upper _ _ _ [34,129,257,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37281

theorem m42873_12 : Upper (D 6) (R 6) [34,129,257,80,12] 13 :=
  permutation_upper _ _ _ [34,129,257,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37289

theorem m42873_34 : Upper (D 6) (R 6) [34,129,257,80,34] 13 :=
  permutation_upper _ _ _ [34,129,257,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37292

theorem m42873_36 : Upper (D 6) (R 6) [34,129,257,80,36] 13 :=
  permutation_upper _ _ _ [34,129,257,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37295

theorem m42873_40 : Upper (D 6) (R 6) [34,129,257,80,40] 13 :=
  permutation_upper _ _ _ [34,129,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37298

theorem m42873_66 : Upper (D 6) (R 6) [34,129,257,80,66] 13 :=
  permutation_upper _ _ _ [34,129,257,66,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37300

theorem m42873_68 : Upper (D 6) (R 6) [34,129,257,80,68] 13 :=
  permutation_upper _ _ _ [34,129,257,68,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37303

def r42873 : Route 9 := (fun mask => (mask,id))

def c42873 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42873 : Upper (D 6) (R 6) [34,129,257,80] 13 := by
  apply FastRouting.sound _ _ [34,129,257,80] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42873 c42873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42873_6
  · exact m42873_10
  · exact m42873_12
  · exact m42873_34
  · exact m42873_36
  · exact m42873_40
  · exact m42873_66
  · exact m42873_68
  · exact u37305
  · exact u37306

theorem m42874_6 : Upper (D 6) (R 6) [34,129,257,96,6] 13 :=
  permutation_upper _ _ _ [34,129,257,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37276

theorem m42874_10 : Upper (D 6) (R 6) [34,129,257,96,10] 13 :=
  permutation_upper _ _ _ [34,129,257,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37282

theorem m42874_12 : Upper (D 6) (R 6) [34,129,257,96,12] 13 :=
  permutation_upper _ _ _ [34,129,257,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37290

theorem m42874_66 : Upper (D 6) (R 6) [34,129,257,96,66] 13 :=
  permutation_upper _ _ _ [34,129,257,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37301

theorem m42874_68 : Upper (D 6) (R 6) [34,129,257,96,68] 13 :=
  permutation_upper _ _ _ [34,129,257,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37304

theorem m42874_72 : Upper (D 6) (R 6) [34,129,257,96,72] 13 :=
  permutation_upper _ _ _ [34,129,257,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37306

def r42874 : Route 9 := (fun mask => (mask,id))

def c42874 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42874 : Upper (D 6) (R 6) [34,129,257,96] 13 := by
  apply FastRouting.sound _ _ [34,129,257,96] 13 (by decide) (choices 2) [6,10,12,66,68,72] r42874 c42874
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42874_6
  · exact m42874_10
  · exact m42874_12
  · exact m42874_66
  · exact m42874_68
  · exact m42874_72

def r42875 : Route 9 := (fun mask => (mask,id))

def c42875 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42875 : Upper (D 6) (R 6) [34,129,258,5] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5] 13 (by decide) (choices 2) [12,36,40,68,72,96] r42875 c42875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37307
  · exact u37308
  · exact u37309
  · exact u37310
  · exact u37311
  · exact u37312

def r42876 : Route 9 := (fun mask => (mask,id))

def c42876 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42876 : Upper (D 6) (R 6) [34,129,258,17] 13 := by
  apply FastRouting.sound _ _ [34,129,258,17] 13 (by decide) (choices 2) [12,36,40,68,72,96] r42876 c42876
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37313
  · exact u37314
  · exact u37315
  · exact u37316
  · exact u37317
  · exact u37318

theorem m42877_5 : Upper (D 6) (R 6) [34,129,258,20,5] 13 :=
  permutation_upper _ _ _ [34,129,258,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37307

theorem m42877_9 : Upper (D 6) (R 6) [34,129,258,20,9] 13 :=
  permutation_upper _ _ _ [34,129,258,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37313

def r42877 : Route 9 := (fun mask => (mask,id))

def c42877 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42877 : Upper (D 6) (R 6) [34,129,258,20] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42877 c42877
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42877_5
  · exact m42877_9
  · exact u37319
  · exact u37320
  · exact u37321
  · exact u37322
  · exact u37323
  · exact u37324
  · exact u37325
  · exact u37326

def b42878 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 262 41 92 124 92 220 348), lower := (rows 35 131 262 41 16 32 64 128 256), losses := [] }

theorem u42878 : Upper (D 6) (R 6) [34,129,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42879_5 : Upper (D 6) (R 6) [34,129,258,36,5] 13 :=
  permutation_upper _ _ _ [34,129,258,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37308

theorem m42879_9 : Upper (D 6) (R 6) [34,129,258,36,9] 13 :=
  permutation_upper _ _ _ [34,129,258,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37314

theorem m42879_12 : Upper (D 6) (R 6) [34,129,258,36,12] 13 :=
  permutation_upper _ _ _ [34,129,258,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37321

def r42879 : Route 9 := (fun mask => (mask,id))

def c42879 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42879 : Upper (D 6) (R 6) [34,129,258,36] 13 := by
  apply FastRouting.sound _ _ [34,129,258,36] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42879 c42879
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42879_5
  · exact m42879_9
  · exact m42879_12
  · exact u37329
  · exact u37330
  · exact u37331

theorem m42880_5 : Upper (D 6) (R 6) [34,129,258,48,5] 13 :=
  permutation_upper _ _ _ [34,129,258,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37309

theorem m42880_9 : Upper (D 6) (R 6) [34,129,258,48,9] 13 :=
  permutation_upper _ _ _ [34,129,258,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37315

theorem m42880_12 : Upper (D 6) (R 6) [34,129,258,48,12] 13 :=
  permutation_upper _ _ _ [34,129,258,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37322

def r42880 : Route 9 := (fun mask => (mask,id))

def c42880 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42880 : Upper (D 6) (R 6) [34,129,258,48] 13 := by
  apply FastRouting.sound _ _ [34,129,258,48] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42880 c42880
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42880_5
  · exact m42880_9
  · exact m42880_12
  · exact u37332
  · exact u37333
  · exact u37334

theorem m42881_12 : Upper (D 6) (R 6) [34,129,258,65,12] 13 :=
  permutation_upper _ _ _ [34,129,258,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37323

theorem m42881_36 : Upper (D 6) (R 6) [34,129,258,65,36] 13 :=
  permutation_upper _ _ _ [34,129,258,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37329

theorem m42881_40 : Upper (D 6) (R 6) [34,129,258,65,40] 13 :=
  permutation_upper _ _ _ [34,129,258,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37332

def r42881 : Route 9 := (fun mask => (mask,id))

def c42881 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42881 : Upper (D 6) (R 6) [34,129,258,65] 13 := by
  apply FastRouting.sound _ _ [34,129,258,65] 13 (by decide) (choices 2) [12,36,40,68,72,96] r42881 c42881
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42881_12
  · exact m42881_36
  · exact m42881_40
  · exact u37335
  · exact u37336
  · exact u37337

theorem m42882_5 : Upper (D 6) (R 6) [34,129,258,68,5] 13 :=
  permutation_upper _ _ _ [34,129,258,5,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37310

theorem m42882_9 : Upper (D 6) (R 6) [34,129,258,68,9] 13 :=
  permutation_upper _ _ _ [34,129,258,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37316

theorem m42882_12 : Upper (D 6) (R 6) [34,129,258,68,12] 13 :=
  permutation_upper _ _ _ [34,129,258,20,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37324

theorem m42882_33 : Upper (D 6) (R 6) [34,129,258,68,33] 13 :=
  permutation_upper _ _ _ [34,129,258,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37327

theorem m42882_36 : Upper (D 6) (R 6) [34,129,258,68,36] 13 :=
  permutation_upper _ _ _ [34,129,258,36,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37330

theorem m42882_40 : Upper (D 6) (R 6) [34,129,258,68,40] 13 :=
  permutation_upper _ _ _ [34,129,258,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37333

theorem m42882_65 : Upper (D 6) (R 6) [34,129,258,68,65] 13 :=
  permutation_upper _ _ _ [34,129,258,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37335

def r42882 : Route 9 := (fun mask => (mask,id))

def c42882 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42882 : Upper (D 6) (R 6) [34,129,258,68] 13 := by
  apply FastRouting.sound _ _ [34,129,258,68] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42882 c42882
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42882_5
  · exact m42882_9
  · exact m42882_12
  · exact m42882_33
  · exact m42882_36
  · exact m42882_40
  · exact m42882_65
  · exact u37338
  · exact u37339
  · exact u37340

theorem m42883_5 : Upper (D 6) (R 6) [34,129,258,80,5] 13 :=
  permutation_upper _ _ _ [34,129,258,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37311

theorem m42883_9 : Upper (D 6) (R 6) [34,129,258,80,9] 13 :=
  permutation_upper _ _ _ [34,129,258,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37317

theorem m42883_12 : Upper (D 6) (R 6) [34,129,258,80,12] 13 :=
  permutation_upper _ _ _ [34,129,258,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37325

theorem m42883_33 : Upper (D 6) (R 6) [34,129,258,80,33] 13 :=
  permutation_upper _ _ _ [34,129,258,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37328

theorem m42883_36 : Upper (D 6) (R 6) [34,129,258,80,36] 13 :=
  permutation_upper _ _ _ [34,129,258,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37331

theorem m42883_40 : Upper (D 6) (R 6) [34,129,258,80,40] 13 :=
  permutation_upper _ _ _ [34,129,258,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37334

theorem m42883_65 : Upper (D 6) (R 6) [34,129,258,80,65] 13 :=
  permutation_upper _ _ _ [34,129,258,65,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37336

theorem m42883_68 : Upper (D 6) (R 6) [34,129,258,80,68] 13 :=
  permutation_upper _ _ _ [34,129,258,68,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37339

def r42883 : Route 9 := (fun mask => (mask,id))

def c42883 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42883 : Upper (D 6) (R 6) [34,129,258,80] 13 := by
  apply FastRouting.sound _ _ [34,129,258,80] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42883 c42883
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42883_5
  · exact m42883_9
  · exact m42883_12
  · exact m42883_33
  · exact m42883_36
  · exact m42883_40
  · exact m42883_65
  · exact m42883_68
  · exact u37341
  · exact u37342

theorem m42884_5 : Upper (D 6) (R 6) [34,129,258,96,5] 13 :=
  permutation_upper _ _ _ [34,129,258,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37312

theorem m42884_9 : Upper (D 6) (R 6) [34,129,258,96,9] 13 :=
  permutation_upper _ _ _ [34,129,258,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37318

theorem m42884_12 : Upper (D 6) (R 6) [34,129,258,96,12] 13 :=
  permutation_upper _ _ _ [34,129,258,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37326

theorem m42884_65 : Upper (D 6) (R 6) [34,129,258,96,65] 13 :=
  permutation_upper _ _ _ [34,129,258,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37337

theorem m42884_68 : Upper (D 6) (R 6) [34,129,258,96,68] 13 :=
  permutation_upper _ _ _ [34,129,258,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37340

theorem m42884_72 : Upper (D 6) (R 6) [34,129,258,96,72] 13 :=
  permutation_upper _ _ _ [34,129,258,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37342

def r42884 : Route 9 := (fun mask => (mask,id))

def c42884 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42884 : Upper (D 6) (R 6) [34,129,258,96] 13 := by
  apply FastRouting.sound _ _ [34,129,258,96] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42884 c42884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42884_5
  · exact m42884_9
  · exact m42884_12
  · exact m42884_65
  · exact m42884_68
  · exact m42884_72

def b42885 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 268 11 116 116 116 244 372), lower := (rows 35 131 268 11 16 32 64 128 256), losses := [] }

theorem u42885 : Upper (D 6) (R 6) [34,129,264,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42886 : Route 9 := (fun mask => (mask,id))

def c42886 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42886 : Upper (D 6) (R 6) [34,129,264,5] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42886 c42886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37343
  · exact u37344
  · exact u37345
  · exact u37346
  · exact u37347
  · exact u37348

def r42887 : Route 9 := (fun mask => (mask,id))

def c42887 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42887 : Upper (D 6) (R 6) [34,129,264,6] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42887 c42887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37349
  · exact u37350
  · exact u37351
  · exact u37352
  · exact u37353
  · exact u37354

def r42888 : Route 9 := (fun mask => (mask,id))

def c42888 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42888 : Upper (D 6) (R 6) [34,129,264,17] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42888 c42888
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37355
  · exact u37356
  · exact u37357
  · exact u37358
  · exact u37359
  · exact u37360

def r42889 : Route 9 := (fun mask => (mask,id))

def c42889 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42889 : Upper (D 6) (R 6) [34,129,264,18] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42889 c42889
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37361
  · exact u37362
  · exact u37363
  · exact u37364
  · exact u37365
  · exact u37366

def r42890 : Route 9 := (fun mask => (mask,id))

def c42890 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42890 : Upper (D 6) (R 6) [34,129,264,20] 13 := by
  apply FastRouting.sound _ _ [34,129,264,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42890 c42890
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37367
  · exact u37368
  · exact u37369
  · exact u37370
  · exact u37371
  · exact u37372
  · exact u37373
  · exact u37374
  · exact u37375
  · exact u37376

def b42891 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 268 41 86 118 86 214 342), lower := (rows 35 131 268 41 16 32 64 128 256), losses := [] }

theorem u42891 : Upper (D 6) (R 6) [34,129,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42892 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 131 268 42 85 117 85 213 341), lower := (rows 35 131 268 42 16 32 64 128 256), losses := [] }

theorem u42892 : Upper (D 6) (R 6) [34,129,264,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42893 : Route 9 := (fun mask => (mask,id))

def c42893 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42893 : Upper (D 6) (R 6) [34,129,264,36] 13 := by
  apply FastRouting.sound _ _ [34,129,264,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42893 c42893
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37377
  · exact u37378
  · exact u37379
  · exact u37380
  · exact u37381
  · exact u37382

def r42894 : Route 9 := (fun mask => (mask,id))

def c42894 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42894 : Upper (D 6) (R 6) [34,129,264,48] 13 := by
  apply FastRouting.sound _ _ [34,129,264,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42894 c42894
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37383
  · exact u37384
  · exact u37385
  · exact u37386
  · exact u37387
  · exact u37388

def r42895 : Route 9 := (fun mask => (mask,id))

def c42895 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42895 : Upper (D 6) (R 6) [34,129,264,65] 13 := by
  apply FastRouting.sound _ _ [34,129,264,65] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42895 c42895
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37389
  · exact u37390
  · exact u37391
  · exact u37392
  · exact u37393
  · exact u37394

def r42896 : Route 9 := (fun mask => (mask,id))

def c42896 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42896 : Upper (D 6) (R 6) [34,129,264,66] 13 := by
  apply FastRouting.sound _ _ [34,129,264,66] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42896 c42896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37395
  · exact u37396
  · exact u37397
  · exact u37398
  · exact u37399
  · exact u37400

def r42897 : Route 9 := (fun mask => (mask,id))

def c42897 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42897 : Upper (D 6) (R 6) [34,129,264,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42897 c42897
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37401
  · exact u37402
  · exact u37403
  · exact u37404
  · exact u37405
  · exact u37406
  · exact u37407
  · exact u37408
  · exact u37409
  · exact u37410

def r42898 : Route 9 := (fun mask => (mask,id))

def c42898 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42898 : Upper (D 6) (R 6) [34,129,264,80] 13 := by
  apply FastRouting.sound _ _ [34,129,264,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42898 c42898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37411
  · exact u37412
  · exact u37413
  · exact u37414
  · exact u37415
  · exact u37416
  · exact u37417
  · exact u37418
  · exact u37419
  · exact u37420

def r42899 : Route 9 := (fun mask => (mask,id))

def c42899 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42899 : Upper (D 6) (R 6) [34,129,264,96] 13 := by
  apply FastRouting.sound _ _ [34,129,264,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42899 c42899
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37421
  · exact u37422
  · exact u37423
  · exact u37424
  · exact u37425
  · exact u37426

#print axioms u42899
end Delivery.IrregularNine14.P06
