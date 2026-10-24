import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0619
import IrregularNine14P07C0620
import IrregularNine14P07C0621
import IrregularNine14P07C0622
import IrregularNine14P07C0623

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r42900 : Route 9 := (fun mask => (mask,id))

def c42900 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42900 : Upper (D 7) (R 7) [36,72,130,272] 13 := by
  apply FastRouting.sound _ _ [36,72,130,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42900 c42900
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37167
  · exact u37168
  · exact u37169
  · exact u37170
  · exact u37171
  · exact u37172
  · exact u37173
  · exact u37174
  · exact u37175
  · exact u37176

def r42901 : Route 9 := (fun mask => (mask,id))

def c42901 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42901 : Upper (D 7) (R 7) [36,72,130,288] 13 := by
  apply FastRouting.sound _ _ [36,72,130,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42901 c42901
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37177
  · exact u37178
  · exact u37179
  · exact u37180
  · exact u37181
  · exact u37182

def b42902 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 181, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 134 328 179 179 243 179 435), lower := (rows 37 74 134 328 16 32 64 128 256), losses := [] }

theorem u42902 : Upper (D 7) (R 7) [36,72,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42903 : Route 9 := (fun mask => (mask,id))

def c42903 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42903 : Upper (D 7) (R 7) [36,72,130,384] 13 := by
  apply FastRouting.sound _ _ [36,72,130,384] 13 (by decide) (choices 2) [3,33,34,65,66,96] r42903 c42903
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37183
  · exact u37184
  · exact u37185
  · exact u37186
  · exact u37187
  · exact u37188

def r42904 : Route 9 := (fun mask => (mask,id))

def c42904 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 2 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42904 : Upper (D 7) (R 7) [36,72,144,160] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160] 13 (by decide) (choices 2) [3,65,66,257,258,320] r42904 c42904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37189
  · exact u37190
  · exact u37191
  · exact u37192
  · exact u37193
  · exact u37194

def b42905 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 148 200 307 291 355 419 291), lower := (rows 37 74 148 200 16 32 64 128 256), losses := [] }

theorem u42905 : Upper (D 7) (R 7) [36,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42906 : Route 9 := (fun mask => (mask,id))

def c42906 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42906 : Upper (D 7) (R 7) [36,72,144,257] 13 := by
  apply FastRouting.sound _ _ [36,72,144,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42906 c42906
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37195
  · exact u37196
  · exact u37197
  · exact u37198
  · exact u37199
  · exact u37200
  · exact u37201
  · exact u37202
  · exact u37203
  · exact u37204

def r42907 : Route 9 := (fun mask => (mask,id))

def c42907 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42907 : Upper (D 7) (R 7) [36,72,144,258] 13 := by
  apply FastRouting.sound _ _ [36,72,144,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42907 c42907
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37205
  · exact u37206
  · exact u37207
  · exact u37208
  · exact u37209
  · exact u37210
  · exact u37211
  · exact u37212
  · exact u37213
  · exact u37214

def r42908 : Route 9 := (fun mask => (mask,id))

def c42908 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42908 : Upper (D 7) (R 7) [36,72,144,288] 13 := by
  apply FastRouting.sound _ _ [36,72,144,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42908 c42908
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37215
  · exact u37216
  · exact u37217
  · exact u37218
  · exact u37219
  · exact u37220

def b42909 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 181, targets := 64 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 74 148 328 179 163 227 163 419), lower := (rows 37 74 148 328 16 32 64 128 256), losses := [] }

theorem u42909 : Upper (D 7) (R 7) [36,72,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42910 : Route 9 := (fun mask => (mask,id))

def c42910 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42910 : Upper (D 7) (R 7) [36,72,144,384] 13 := by
  apply FastRouting.sound _ _ [36,72,144,384] 13 (by decide) (choices 2) [3,33,34,65,66,96] r42910 c42910
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37221
  · exact u37222
  · exact u37223
  · exact u37224
  · exact u37225
  · exact u37226

def b42911 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 164 265 211 243 211 211 467), lower := (rows 37 74 164 265 16 32 64 128 256), losses := [] }

theorem u42911 : Upper (D 7) (R 7) [36,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42912 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 164 266 211 243 211 211 467), lower := (rows 37 74 164 266 16 32 64 128 256), losses := [] }

theorem u42912 : Upper (D 7) (R 7) [36,72,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42913 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 164 280 211 227 195 195 451), lower := (rows 37 74 164 280 16 32 64 128 256), losses := [] }

theorem u42913 : Upper (D 7) (R 7) [36,72,160,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42914 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 74 164 392 83 115 83 211 339), lower := (rows 37 74 164 392 16 32 64 128 256), losses := [] }

theorem u42914 : Upper (D 7) (R 7) [36,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42915_258 : Upper (D 7) (R 7) [36,72,192,160,258] 13 :=
  permutation_upper _ _ _ [36,72,192,160,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37228

def r42915 : Route 9 := (fun mask => (mask,id))

def c42915 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42915 : Upper (D 7) (R 7) [36,72,192,160] 13 := by
  apply FastRouting.sound _ _ [36,72,192,160] 13 (by decide) (choices 2) [3,257,258] r42915 c42915
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37227
  · exact u37228
  · exact m42915_258

def r42916 : Route 9 := (fun mask => (mask,id))

def c42916 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42916 : Upper (D 7) (R 7) [36,72,192,257] 13 := by
  apply FastRouting.sound _ _ [36,72,192,257] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42916 c42916
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37229
  · exact u37230
  · exact u37231
  · exact u37232
  · exact u37233
  · exact u37234

def r42917 : Route 9 := (fun mask => (mask,id))

def c42917 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42917 : Upper (D 7) (R 7) [36,72,192,258] 13 := by
  apply FastRouting.sound _ _ [36,72,192,258] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42917 c42917
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37235
  · exact u37236
  · exact u37237
  · exact u37238
  · exact u37239
  · exact u37240

def r42918 : Route 9 := (fun mask => (mask,id))

def c42918 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42918 : Upper (D 7) (R 7) [36,72,192,272] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42918 c42918
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37241
  · exact u37242
  · exact u37243
  · exact u37244
  · exact u37245
  · exact u37246

def r42919 : Route 9 := (fun mask => (mask,id))

def c42919 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42919 : Upper (D 7) (R 7) [36,72,192,288] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288] 13 (by decide) (choices 2) [3,129,130] r42919 c42919
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37247
  · exact u37248
  · exact u37249

def r42920 : Route 9 := (fun mask => (mask,id))

def c42920 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42920 : Upper (D 7) (R 7) [36,72,192,384] 13 := by
  apply FastRouting.sound _ _ [36,72,192,384] 13 (by decide) (choices 2) [3,33,34] r42920 c42920
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37250
  · exact u37251
  · exact u37252

def b42921 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 11 466 498 466 466 466), lower := (rows 37 98 13 11 16 32 64 128 256), losses := [] }

theorem u42921 : Upper (D 7) (R 7) [36,96,9,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42922 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 98 13 25 466 482 450 450 450), lower := (rows 37 98 13 25 16 32 64 128 256), losses := [] }

theorem u42922 : Upper (D 7) (R 7) [36,96,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42923 : Route 9 := (fun mask => (mask,id))

def c42923 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42923 : Upper (D 7) (R 7) [36,96,9,18] 13 := by
  apply FastRouting.sound _ _ [36,96,9,18] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42923 c42923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37253
  · exact u37254
  · exact u37255
  · exact u37256
  · exact u37257
  · exact u37258
  · exact u37259
  · exact u37260
  · exact u37261
  · exact u37262

def b42924 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 98 13 73 402 434 466 402 402), lower := (rows 37 98 13 73 16 32 64 128 256), losses := [] }

theorem u42924 : Upper (D 7) (R 7) [36,96,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42925 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 13, targets := 128 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 37 98 13 74 403 435 467 403 403), lower := (rows 37 98 13 74 16 32 64 128 256), losses := [] }

theorem u42925 : Upper (D 7) (R 7) [36,96,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42926 : Route 9 := (fun mask => (mask,id))

def c42926 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42926 : Upper (D 7) (R 7) [36,96,9,80] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42926 c42926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37263
  · exact u37264
  · exact u37265
  · exact u37266
  · exact u37267
  · exact u37268

def b42927 : PairBound 9 := { available := 466, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 98 13 137 466 498 466 466 466), lower := (rows 37 98 13 137 16 32 64 128 256), losses := [] }

theorem u42927 : Upper (D 7) (R 7) [36,96,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42928 : Route 9 := (fun mask => (mask,id))

def c42928 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42928 : Upper (D 7) (R 7) [36,96,9,130] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42928 c42928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37269
  · exact u37270
  · exact u37271
  · exact u37272
  · exact u37273
  · exact u37274
  · exact u37275
  · exact u37276
  · exact u37277
  · exact u37278

def r42929 : Route 9 := (fun mask => (mask,id))

def c42929 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42929 : Upper (D 7) (R 7) [36,96,9,144] 13 := by
  apply FastRouting.sound _ _ [36,96,9,144] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42929 c42929
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37279
  · exact u37280
  · exact u37281
  · exact u37282
  · exact u37283
  · exact u37284
  · exact u37285
  · exact u37286
  · exact u37287
  · exact u37288

def r42930 : Route 9 := (fun mask => (mask,id))

def c42930 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42930 : Upper (D 7) (R 7) [36,96,9,192] 13 := by
  apply FastRouting.sound _ _ [36,96,9,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42930 c42930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37289
  · exact u37290
  · exact u37291
  · exact u37292
  · exact u37293
  · exact u37294

def b42931 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 98 13 265 210 242 210 210 466), lower := (rows 37 98 13 265 16 32 64 128 256), losses := [] }

theorem u42931 : Upper (D 7) (R 7) [36,96,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42932 : Route 9 := (fun mask => (mask,id))

def c42932 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42932 : Upper (D 7) (R 7) [36,96,9,258] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42932 c42932
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37295
  · exact u37296
  · exact u37297
  · exact u37298
  · exact u37299
  · exact u37300

def r42933 : Route 9 := (fun mask => (mask,id))

def c42933 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42933 : Upper (D 7) (R 7) [36,96,9,272] 13 := by
  apply FastRouting.sound _ _ [36,96,9,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42933 c42933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37301
  · exact u37302
  · exact u37303
  · exact u37304
  · exact u37305
  · exact u37306

def r42934 : Route 9 := (fun mask => (mask,id))

def c42934 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42934 : Upper (D 7) (R 7) [36,96,9,320] 13 := by
  apply FastRouting.sound _ _ [36,96,9,320] 13 (by decide) (choices 2) [3,129,130] r42934 c42934
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37307
  · exact u37308
  · exact u37309

def r42935 : Route 9 := (fun mask => (mask,id))

def c42935 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42935 : Upper (D 7) (R 7) [36,96,9,384] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42935 c42935
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37310
  · exact u37311
  · exact u37312
  · exact u37313
  · exact u37314
  · exact u37315

def b42936 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 14 11 465 497 465 465 465), lower := (rows 37 98 14 11 16 32 64 128 256), losses := [] }

theorem u42936 : Upper (D 7) (R 7) [36,96,10,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42937 : Route 9 := (fun mask => (mask,id))

def c42937 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42937 : Upper (D 7) (R 7) [36,96,10,17] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42937 c42937
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37316
  · exact u37317
  · exact u37318
  · exact u37319
  · exact u37320
  · exact u37321
  · exact u37322
  · exact u37323
  · exact u37324
  · exact u37325

def b42938 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 98 14 26 465 481 449 449 449), lower := (rows 37 98 14 26 16 32 64 128 256), losses := [] }

theorem u42938 : Upper (D 7) (R 7) [36,96,10,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42939 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 13, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 37 98 14 73 403 435 467 403 403), lower := (rows 37 98 14 73 16 32 64 128 256), losses := [] }

theorem u42939 : Upper (D 7) (R 7) [36,96,10,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42939 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42940 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 14 74 401 433 465 401 401), lower := (rows 37 98 14 74 16 32 64 128 256), losses := [] }

theorem u42940 : Upper (D 7) (R 7) [36,96,10,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42941 : Route 9 := (fun mask => (mask,id))

def c42941 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42941 : Upper (D 7) (R 7) [36,96,10,80] 13 := by
  apply FastRouting.sound _ _ [36,96,10,80] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42941 c42941
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37326
  · exact u37327
  · exact u37328
  · exact u37329
  · exact u37330
  · exact u37331

def r42942 : Route 9 := (fun mask => (mask,id))

def c42942 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42942 : Upper (D 7) (R 7) [36,96,10,129] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42942 c42942
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37332
  · exact u37333
  · exact u37334
  · exact u37335
  · exact u37336
  · exact u37337
  · exact u37338
  · exact u37339
  · exact u37340
  · exact u37341

def b42943 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 98 14 138 465 497 465 465 465), lower := (rows 37 98 14 138 16 32 64 128 256), losses := [] }

theorem u42943 : Upper (D 7) (R 7) [36,96,10,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42944 : Route 9 := (fun mask => (mask,id))

def c42944 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42944 : Upper (D 7) (R 7) [36,96,10,144] 13 := by
  apply FastRouting.sound _ _ [36,96,10,144] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42944 c42944
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37342
  · exact u37343
  · exact u37344
  · exact u37345
  · exact u37346
  · exact u37347
  · exact u37348
  · exact u37349
  · exact u37350
  · exact u37351

def r42945 : Route 9 := (fun mask => (mask,id))

def c42945 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42945 : Upper (D 7) (R 7) [36,96,10,192] 13 := by
  apply FastRouting.sound _ _ [36,96,10,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42945 c42945
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37352
  · exact u37353
  · exact u37354
  · exact u37355
  · exact u37356
  · exact u37357

def r42946 : Route 9 := (fun mask => (mask,id))

def c42946 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42946 : Upper (D 7) (R 7) [36,96,10,257] 13 := by
  apply FastRouting.sound _ _ [36,96,10,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42946 c42946
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37358
  · exact u37359
  · exact u37360
  · exact u37361
  · exact u37362
  · exact u37363

def b42947 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 37 98 14 266 209 241 209 209 465), lower := (rows 37 98 14 266 16 32 64 128 256), losses := [] }

theorem u42947 : Upper (D 7) (R 7) [36,96,10,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42948 : Route 9 := (fun mask => (mask,id))

def c42948 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42948 : Upper (D 7) (R 7) [36,96,10,272] 13 := by
  apply FastRouting.sound _ _ [36,96,10,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42948 c42948
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37364
  · exact u37365
  · exact u37366
  · exact u37367
  · exact u37368
  · exact u37369

def r42949 : Route 9 := (fun mask => (mask,id))

def c42949 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42949 : Upper (D 7) (R 7) [36,96,10,320] 13 := by
  apply FastRouting.sound _ _ [36,96,10,320] 13 (by decide) (choices 2) [3,129,130] r42949 c42949
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37370
  · exact u37371
  · exact u37372

def r42950 : Route 9 := (fun mask => (mask,id))

def c42950 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42950 : Upper (D 7) (R 7) [36,96,10,384] 13 := by
  apply FastRouting.sound _ _ [36,96,10,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42950 c42950
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37373
  · exact u37374
  · exact u37375
  · exact u37376
  · exact u37377
  · exact u37378

def r42951 : Route 9 := (fun mask => (mask,id))

def c42951 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42951 : Upper (D 7) (R 7) [36,96,24,3] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42951 c42951
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37379
  · exact u37380
  · exact u37381
  · exact u37382
  · exact u37383
  · exact u37384
  · exact u37385
  · exact u37386
  · exact u37387
  · exact u37388

theorem m42952_3 : Upper (D 7) (R 7) [36,96,24,65,3] 13 :=
  permutation_upper _ _ _ [36,96,24,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37380

def r42952 : Route 9 := (fun mask => (mask,id))

def c42952 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42952 : Upper (D 7) (R 7) [36,96,24,65] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42952 c42952
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42952_3
  · exact u37389
  · exact u37390
  · exact u37391
  · exact u37392
  · exact u37393

def b42953 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 28 74 403 419 451 387 387), lower := (rows 37 98 28 74 16 32 64 128 256), losses := [] }

theorem u42953 : Upper (D 7) (R 7) [36,96,24,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42954_3 : Upper (D 7) (R 7) [36,96,24,129,3] 13 :=
  permutation_upper _ _ _ [36,96,24,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37382

theorem m42954_65 : Upper (D 7) (R 7) [36,96,24,129,65] 13 :=
  permutation_upper _ _ _ [36,96,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37389

theorem m42954_66 : Upper (D 7) (R 7) [36,96,24,129,66] 13 :=
  permutation_upper _ _ _ [36,96,24,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37394

def r42954 : Route 9 := (fun mask => (mask,id))

def c42954 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42954 : Upper (D 7) (R 7) [36,96,24,129] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42954 c42954
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42954_3
  · exact m42954_65
  · exact m42954_66
  · exact u37399
  · exact u37400
  · exact u37401
  · exact u37402
  · exact u37403
  · exact u37404
  · exact u37405

theorem m42955_3 : Upper (D 7) (R 7) [36,96,24,130,3] 13 :=
  permutation_upper _ _ _ [36,96,24,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37383

theorem m42955_65 : Upper (D 7) (R 7) [36,96,24,130,65] 13 :=
  permutation_upper _ _ _ [36,96,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37390

theorem m42955_66 : Upper (D 7) (R 7) [36,96,24,130,66] 13 :=
  permutation_upper _ _ _ [36,96,24,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37395

theorem m42955_129 : Upper (D 7) (R 7) [36,96,24,130,129] 13 :=
  permutation_upper _ _ _ [36,96,24,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37400

def r42955 : Route 9 := (fun mask => (mask,id))

def c42955 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42955 : Upper (D 7) (R 7) [36,96,24,130] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42955 c42955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42955_3
  · exact m42955_65
  · exact m42955_66
  · exact m42955_129
  · exact u37406
  · exact u37407
  · exact u37408
  · exact u37409
  · exact u37410
  · exact u37411

theorem m42956_3 : Upper (D 7) (R 7) [36,96,24,192,3] 13 :=
  permutation_upper _ _ _ [36,96,24,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37384

theorem m42956_129 : Upper (D 7) (R 7) [36,96,24,192,129] 13 :=
  permutation_upper _ _ _ [36,96,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37401

theorem m42956_130 : Upper (D 7) (R 7) [36,96,24,192,130] 13 :=
  permutation_upper _ _ _ [36,96,24,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37407

def r42956 : Route 9 := (fun mask => (mask,id))

def c42956 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42956 : Upper (D 7) (R 7) [36,96,24,192] 13 := by
  apply FastRouting.sound _ _ [36,96,24,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42956 c42956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42956_3
  · exact m42956_129
  · exact m42956_130
  · exact u37412
  · exact u37413
  · exact u37414

theorem m42957_3 : Upper (D 7) (R 7) [36,96,24,257,3] 13 :=
  permutation_upper _ _ _ [36,96,24,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37385

theorem m42957_65 : Upper (D 7) (R 7) [36,96,24,257,65] 13 :=
  permutation_upper _ _ _ [36,96,24,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37391

theorem m42957_66 : Upper (D 7) (R 7) [36,96,24,257,66] 13 :=
  permutation_upper _ _ _ [36,96,24,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37396

theorem m42957_129 : Upper (D 7) (R 7) [36,96,24,257,129] 13 :=
  permutation_upper _ _ _ [36,96,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37402

theorem m42957_130 : Upper (D 7) (R 7) [36,96,24,257,130] 13 :=
  permutation_upper _ _ _ [36,96,24,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37408

theorem m42957_192 : Upper (D 7) (R 7) [36,96,24,257,192] 13 :=
  permutation_upper _ _ _ [36,96,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37412

def r42957 : Route 9 := (fun mask => (mask,id))

def c42957 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42957 : Upper (D 7) (R 7) [36,96,24,257] 13 := by
  apply FastRouting.sound _ _ [36,96,24,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42957 c42957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42957_3
  · exact m42957_65
  · exact m42957_66
  · exact m42957_129
  · exact m42957_130
  · exact m42957_192

theorem m42958_3 : Upper (D 7) (R 7) [36,96,24,258,3] 13 :=
  permutation_upper _ _ _ [36,96,24,3,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37386

theorem m42958_65 : Upper (D 7) (R 7) [36,96,24,258,65] 13 :=
  permutation_upper _ _ _ [36,96,24,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37392

theorem m42958_66 : Upper (D 7) (R 7) [36,96,24,258,66] 13 :=
  permutation_upper _ _ _ [36,96,24,66,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37397

theorem m42958_129 : Upper (D 7) (R 7) [36,96,24,258,129] 13 :=
  permutation_upper _ _ _ [36,96,24,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37403

theorem m42958_130 : Upper (D 7) (R 7) [36,96,24,258,130] 13 :=
  permutation_upper _ _ _ [36,96,24,130,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37409

theorem m42958_192 : Upper (D 7) (R 7) [36,96,24,258,192] 13 :=
  permutation_upper _ _ _ [36,96,24,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37413

def r42958 : Route 9 := (fun mask => (mask,id))

def c42958 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42958 : Upper (D 7) (R 7) [36,96,24,258] 13 := by
  apply FastRouting.sound _ _ [36,96,24,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42958 c42958
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42958_3
  · exact m42958_65
  · exact m42958_66
  · exact m42958_129
  · exact m42958_130
  · exact m42958_192

theorem m42959_3 : Upper (D 7) (R 7) [36,96,24,320,3] 13 :=
  permutation_upper _ _ _ [36,96,24,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37387

theorem m42959_129 : Upper (D 7) (R 7) [36,96,24,320,129] 13 :=
  permutation_upper _ _ _ [36,96,24,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37404

theorem m42959_130 : Upper (D 7) (R 7) [36,96,24,320,130] 13 :=
  permutation_upper _ _ _ [36,96,24,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37410

def r42959 : Route 9 := (fun mask => (mask,id))

def c42959 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42959 : Upper (D 7) (R 7) [36,96,24,320] 13 := by
  apply FastRouting.sound _ _ [36,96,24,320] 13 (by decide) (choices 2) [3,129,130] r42959 c42959
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m42959_3
  · exact m42959_129
  · exact m42959_130

#print axioms u42959
end Delivery.IrregularNine14.P07
