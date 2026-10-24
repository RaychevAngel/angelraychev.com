import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0637
import IrregularNine14P06C0638
import IrregularNine14P06C0639
import IrregularNine14P06C0640
import IrregularNine14P06C0641
import IrregularNine14P06C0642

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r43080 : Route 9 := (fun mask => (mask,id))

def c43080 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43080 : Upper (D 6) (R 6) [34,136,96,20] 13 := by
  apply FastRouting.sound _ _ [34,136,96,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43080 c43080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38247
  · exact u38248
  · exact u38249
  · exact u38250
  · exact u38251
  · exact u38252
  · exact u38253
  · exact u38254
  · exact u38255
  · exact u38256

def r43081 : Route 9 := (fun mask => (mask,id))

def c43081 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43081 : Upper (D 6) (R 6) [34,136,96,65] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43081 c43081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38257
  · exact u38258
  · exact u38259
  · exact u38260
  · exact u38261
  · exact u38262

def r43082 : Route 9 := (fun mask => (mask,id))

def c43082 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43082 : Upper (D 6) (R 6) [34,136,96,66] 13 := by
  apply FastRouting.sound _ _ [34,136,96,66] 13 (by decide) (choices 2) [5,257,260] r43082 c43082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38263
  · exact u38264
  · exact u38265

def b43083 : PairBound 9 := { available := 279, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 100 76 279 311 343 407 279), lower := (rows 35 138 100 76 16 32 64 128 256), losses := [] }

theorem u43083 : Upper (D 6) (R 6) [34,136,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43084 : Route 9 := (fun mask => (mask,id))

def c43084 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43084 : Upper (D 6) (R 6) [34,136,96,80] 13 := by
  apply FastRouting.sound _ _ [34,136,96,80] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43084 c43084
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38266
  · exact u38267
  · exact u38268
  · exact u38269
  · exact u38270
  · exact u38271

def r43085 : Route 9 := (fun mask => (mask,id))

def c43085 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43085 : Upper (D 6) (R 6) [34,136,96,257] 13 := by
  apply FastRouting.sound _ _ [34,136,96,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43085 c43085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38272
  · exact u38273
  · exact u38274
  · exact u38275
  · exact u38276
  · exact u38277

def r43086 : Route 9 := (fun mask => (mask,id))

def c43086 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43086 : Upper (D 6) (R 6) [34,136,96,258] 13 := by
  apply FastRouting.sound _ _ [34,136,96,258] 13 (by decide) (choices 2) [5,65,68] r43086 c43086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38278
  · exact u38279
  · exact u38280

def r43087 : Route 9 := (fun mask => (mask,id))

def c43087 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43087 : Upper (D 6) (R 6) [34,136,96,260] 13 := by
  apply FastRouting.sound _ _ [34,136,96,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43087 c43087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38281
  · exact u38282
  · exact u38283
  · exact u38284
  · exact u38285
  · exact u38286

def r43088 : Route 9 := (fun mask => (mask,id))

def c43088 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43088 : Upper (D 6) (R 6) [34,136,96,272] 13 := by
  apply FastRouting.sound _ _ [34,136,96,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43088 c43088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38287
  · exact u38288
  · exact u38289
  · exact u38290
  · exact u38291
  · exact u38292

def r43089 : Route 9 := (fun mask => (mask,id))

def c43089 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43089 : Upper (D 6) (R 6) [34,136,96,320] 13 := by
  apply FastRouting.sound _ _ [34,136,96,320] 13 (by decide) (choices 2) [3,5,6] r43089 c43089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38293
  · exact u38294
  · exact u38295

def b43090 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 261 11 116 116 116 244 372), lower := (rows 35 138 261 11 16 32 64 128 256), losses := [] }

theorem u43090 : Upper (D 6) (R 6) [34,136,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43091 : PairBound 9 := { available := 118, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 138 261 13 118 118 118 246 374), lower := (rows 35 138 261 13 16 32 64 128 256), losses := [] }

theorem u43091 : Upper (D 6) (R 6) [34,136,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43092 : Route 9 := (fun mask => (mask,id))

def c43092 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43092 : Upper (D 6) (R 6) [34,136,257,6] 13 := by
  apply FastRouting.sound _ _ [34,136,257,6] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43092 c43092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38296
  · exact u38297
  · exact u38298
  · exact u38299
  · exact u38300
  · exact u38301

def r43093 : Route 9 := (fun mask => (mask,id))

def c43093 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43093 : Upper (D 6) (R 6) [34,136,257,17] 13 := by
  apply FastRouting.sound _ _ [34,136,257,17] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43093 c43093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38302
  · exact u38303
  · exact u38304
  · exact u38305
  · exact u38306
  · exact u38307

def r43094 : Route 9 := (fun mask => (mask,id))

def c43094 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43094 : Upper (D 6) (R 6) [34,136,257,18] 13 := by
  apply FastRouting.sound _ _ [34,136,257,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43094 c43094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38308
  · exact u38309
  · exact u38310
  · exact u38311
  · exact u38312
  · exact u38313

def r43095 : Route 9 := (fun mask => (mask,id))

def c43095 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43095 : Upper (D 6) (R 6) [34,136,257,20] 13 := by
  apply FastRouting.sound _ _ [34,136,257,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43095 c43095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38314
  · exact u38315
  · exact u38316
  · exact u38317
  · exact u38318
  · exact u38319
  · exact u38320
  · exact u38321
  · exact u38322
  · exact u38323

def b43096 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 261 41 86 118 86 214 342), lower := (rows 35 138 261 41 16 32 64 128 256), losses := [] }

theorem u43096 : Upper (D 6) (R 6) [34,136,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43097 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 261 42 85 117 85 213 341), lower := (rows 35 138 261 42 16 32 64 128 256), losses := [] }

theorem u43097 : Upper (D 6) (R 6) [34,136,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43098 : Route 9 := (fun mask => (mask,id))

def c43098 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43098 : Upper (D 6) (R 6) [34,136,257,36] 13 := by
  apply FastRouting.sound _ _ [34,136,257,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43098 c43098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38324
  · exact u38325
  · exact u38326
  · exact u38327
  · exact u38328
  · exact u38329

def r43099 : Route 9 := (fun mask => (mask,id))

def c43099 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43099 : Upper (D 6) (R 6) [34,136,257,48] 13 := by
  apply FastRouting.sound _ _ [34,136,257,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43099 c43099
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38330
  · exact u38331
  · exact u38332
  · exact u38333
  · exact u38334
  · exact u38335

def r43100 : Route 9 := (fun mask => (mask,id))

def c43100 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43100 : Upper (D 6) (R 6) [34,136,257,65] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65] 13 (by decide) (choices 2) [6,34,36,66,68,96] r43100 c43100
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38336
  · exact u38337
  · exact u38338
  · exact u38339
  · exact u38340
  · exact u38341

def r43101 : Route 9 := (fun mask => (mask,id))

def c43101 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43101 : Upper (D 6) (R 6) [34,136,257,66] 13 := by
  apply FastRouting.sound _ _ [34,136,257,66] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43101 c43101
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38342
  · exact u38343
  · exact u38344
  · exact u38345
  · exact u38346
  · exact u38347

def r43102 : Route 9 := (fun mask => (mask,id))

def c43102 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43102 : Upper (D 6) (R 6) [34,136,257,68] 13 := by
  apply FastRouting.sound _ _ [34,136,257,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43102 c43102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38348
  · exact u38349
  · exact u38350
  · exact u38351
  · exact u38352
  · exact u38353
  · exact u38354
  · exact u38355
  · exact u38356
  · exact u38357

def r43103 : Route 9 := (fun mask => (mask,id))

def c43103 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43103 : Upper (D 6) (R 6) [34,136,257,80] 13 := by
  apply FastRouting.sound _ _ [34,136,257,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43103 c43103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38358
  · exact u38359
  · exact u38360
  · exact u38361
  · exact u38362
  · exact u38363
  · exact u38364
  · exact u38365
  · exact u38366
  · exact u38367

def r43104 : Route 9 := (fun mask => (mask,id))

def c43104 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43104 : Upper (D 6) (R 6) [34,136,257,96] 13 := by
  apply FastRouting.sound _ _ [34,136,257,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43104 c43104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38368
  · exact u38369
  · exact u38370
  · exact u38371
  · exact u38372
  · exact u38373

def r43105 : Route 9 := (fun mask => (mask,id))

def c43105 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43105 : Upper (D 6) (R 6) [34,136,258,5] 13 := by
  apply FastRouting.sound _ _ [34,136,258,5] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43105 c43105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38374
  · exact u38375
  · exact u38376
  · exact u38377
  · exact u38378
  · exact u38379

def r43106 : Route 9 := (fun mask => (mask,id))

def c43106 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43106 : Upper (D 6) (R 6) [34,136,258,17] 13 := by
  apply FastRouting.sound _ _ [34,136,258,17] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43106 c43106
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38380
  · exact u38381
  · exact u38382
  · exact u38383
  · exact u38384
  · exact u38385

def r43107 : Route 9 := (fun mask => (mask,id))

def c43107 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43107 : Upper (D 6) (R 6) [34,136,258,20] 13 := by
  apply FastRouting.sound _ _ [34,136,258,20] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43107 c43107
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38386
  · exact u38387
  · exact u38388
  · exact u38389
  · exact u38390
  · exact u38391

def b43108 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 262 41 85 117 85 213 341), lower := (rows 35 138 262 41 16 32 64 128 256), losses := [] }

theorem u43108 : Upper (D 6) (R 6) [34,136,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43109 : Route 9 := (fun mask => (mask,id))

def c43109 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43109 : Upper (D 6) (R 6) [34,136,258,36] 13 := by
  apply FastRouting.sound _ _ [34,136,258,36] 13 (by decide) (choices 2) [5,65,68] r43109 c43109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38392
  · exact u38393
  · exact u38394

def r43110 : Route 9 := (fun mask => (mask,id))

def c43110 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43110 : Upper (D 6) (R 6) [34,136,258,48] 13 := by
  apply FastRouting.sound _ _ [34,136,258,48] 13 (by decide) (choices 2) [5,65,68] r43110 c43110
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38395
  · exact u38396
  · exact u38397

def r43111 : Route 9 := (fun mask => (mask,id))

def c43111 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43111 : Upper (D 6) (R 6) [34,136,258,65] 13 := by
  apply FastRouting.sound _ _ [34,136,258,65] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43111 c43111
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38398
  · exact u38399
  · exact u38400
  · exact u38401
  · exact u38402
  · exact u38403

def r43112 : Route 9 := (fun mask => (mask,id))

def c43112 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43112 : Upper (D 6) (R 6) [34,136,258,68] 13 := by
  apply FastRouting.sound _ _ [34,136,258,68] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43112 c43112
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38404
  · exact u38405
  · exact u38406
  · exact u38407
  · exact u38408
  · exact u38409

def r43113 : Route 9 := (fun mask => (mask,id))

def c43113 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43113 : Upper (D 6) (R 6) [34,136,258,80] 13 := by
  apply FastRouting.sound _ _ [34,136,258,80] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43113 c43113
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38410
  · exact u38411
  · exact u38412
  · exact u38413
  · exact u38414
  · exact u38415

def r43114 : Route 9 := (fun mask => (mask,id))

def c43114 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43114 : Upper (D 6) (R 6) [34,136,258,96] 13 := by
  apply FastRouting.sound _ _ [34,136,258,96] 13 (by decide) (choices 2) [5,65,68] r43114 c43114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38416
  · exact u38417
  · exact u38418

def b43115 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 276 11 117 101 101 229 357), lower := (rows 35 138 276 11 16 32 64 128 256), losses := [] }

theorem u43115 : Upper (D 6) (R 6) [34,136,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43116 : Route 9 := (fun mask => (mask,id))

def c43116 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43116 : Upper (D 6) (R 6) [34,136,272,5] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43116 c43116
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38419
  · exact u38420
  · exact u38421
  · exact u38422
  · exact u38423
  · exact u38424
  · exact u38425
  · exact u38426
  · exact u38427
  · exact u38428

def r43117 : Route 9 := (fun mask => (mask,id))

def c43117 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43117 : Upper (D 6) (R 6) [34,136,272,6] 13 := by
  apply FastRouting.sound _ _ [34,136,272,6] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43117 c43117
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38429
  · exact u38430
  · exact u38431
  · exact u38432
  · exact u38433
  · exact u38434

def b43118 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 276 41 87 103 71 199 327), lower := (rows 35 138 276 41 16 32 64 128 256), losses := [] }

theorem u43118 : Upper (D 6) (R 6) [34,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43119 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 276 42 85 101 69 197 325), lower := (rows 35 138 276 42 16 32 64 128 256), losses := [] }

theorem u43119 : Upper (D 6) (R 6) [34,136,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43120 : Route 9 := (fun mask => (mask,id))

def c43120 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43120 : Upper (D 6) (R 6) [34,136,272,36] 13 := by
  apply FastRouting.sound _ _ [34,136,272,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43120 c43120
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38435
  · exact u38436
  · exact u38437
  · exact u38438
  · exact u38439
  · exact u38440

def r43121 : Route 9 := (fun mask => (mask,id))

def c43121 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43121 : Upper (D 6) (R 6) [34,136,272,65] 13 := by
  apply FastRouting.sound _ _ [34,136,272,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43121 c43121
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38441
  · exact u38442
  · exact u38443
  · exact u38444
  · exact u38445
  · exact u38446
  · exact u38447
  · exact u38448
  · exact u38449
  · exact u38450

def r43122 : Route 9 := (fun mask => (mask,id))

def c43122 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43122 : Upper (D 6) (R 6) [34,136,272,66] 13 := by
  apply FastRouting.sound _ _ [34,136,272,66] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43122 c43122
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38451
  · exact u38452
  · exact u38453
  · exact u38454
  · exact u38455
  · exact u38456

def r43123 : Route 9 := (fun mask => (mask,id))

def c43123 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43123 : Upper (D 6) (R 6) [34,136,272,68] 13 := by
  apply FastRouting.sound _ _ [34,136,272,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43123 c43123
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38457
  · exact u38458
  · exact u38459
  · exact u38460
  · exact u38461
  · exact u38462
  · exact u38463
  · exact u38464
  · exact u38465
  · exact u38466

def r43124 : Route 9 := (fun mask => (mask,id))

def c43124 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43124 : Upper (D 6) (R 6) [34,136,272,96] 13 := by
  apply FastRouting.sound _ _ [34,136,272,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43124 c43124
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38467
  · exact u38468
  · exact u38469
  · exact u38470
  · exact u38471
  · exact u38472

def b43125 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 292 11 85 117 85 213 341), lower := (rows 35 138 292 11 16 32 64 128 256), losses := [] }

theorem u43125 : Upper (D 6) (R 6) [34,136,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43126 : Route 9 := (fun mask => (mask,id))

def c43126 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43126 : Upper (D 6) (R 6) [34,136,288,5] 13 := by
  apply FastRouting.sound _ _ [34,136,288,5] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43126 c43126
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38473
  · exact u38474
  · exact u38475
  · exact u38476
  · exact u38477
  · exact u38478

def r43127 : Route 9 := (fun mask => (mask,id))

def c43127 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43127 : Upper (D 6) (R 6) [34,136,288,6] 13 := by
  apply FastRouting.sound _ _ [34,136,288,6] 13 (by decide) (choices 2) [5,65,68] r43127 c43127
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38479
  · exact u38480
  · exact u38481

def r43128 : Route 9 := (fun mask => (mask,id))

def c43128 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43128 : Upper (D 6) (R 6) [34,136,288,17] 13 := by
  apply FastRouting.sound _ _ [34,136,288,17] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43128 c43128
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38482
  · exact u38483
  · exact u38484
  · exact u38485
  · exact u38486
  · exact u38487

def r43129 : Route 9 := (fun mask => (mask,id))

def c43129 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43129 : Upper (D 6) (R 6) [34,136,288,18] 13 := by
  apply FastRouting.sound _ _ [34,136,288,18] 13 (by decide) (choices 2) [5,65,68] r43129 c43129
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38488
  · exact u38489
  · exact u38490

def r43130 : Route 9 := (fun mask => (mask,id))

def c43130 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43130 : Upper (D 6) (R 6) [34,136,288,20] 13 := by
  apply FastRouting.sound _ _ [34,136,288,20] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43130 c43130
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38491
  · exact u38492
  · exact u38493
  · exact u38494
  · exact u38495
  · exact u38496

def r43131 : Route 9 := (fun mask => (mask,id))

def c43131 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43131 : Upper (D 6) (R 6) [34,136,288,65] 13 := by
  apply FastRouting.sound _ _ [34,136,288,65] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43131 c43131
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38497
  · exact u38498
  · exact u38499
  · exact u38500
  · exact u38501
  · exact u38502

def r43132 : Route 9 := (fun mask => (mask,id))

def c43132 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43132 : Upper (D 6) (R 6) [34,136,288,66] 13 := by
  apply FastRouting.sound _ _ [34,136,288,66] 13 (by decide) (choices 2) [5,65,68] r43132 c43132
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38503
  · exact u38504
  · exact u38505

def r43133 : Route 9 := (fun mask => (mask,id))

def c43133 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43133 : Upper (D 6) (R 6) [34,136,288,68] 13 := by
  apply FastRouting.sound _ _ [34,136,288,68] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43133 c43133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38506
  · exact u38507
  · exact u38508
  · exact u38509
  · exact u38510
  · exact u38511

def r43134 : Route 9 := (fun mask => (mask,id))

def c43134 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43134 : Upper (D 6) (R 6) [34,136,288,80] 13 := by
  apply FastRouting.sound _ _ [34,136,288,80] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43134 c43134
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38512
  · exact u38513
  · exact u38514
  · exact u38515
  · exact u38516
  · exact u38517

def b43135 : PairBound 9 := { available := 117, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 324 11 117 117 117 245 373), lower := (rows 35 138 324 11 16 32 64 128 256), losses := [] }

theorem u43135 : Upper (D 6) (R 6) [34,136,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43136 : Route 9 := (fun mask => (mask,id))

def c43136 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43136 : Upper (D 6) (R 6) [34,136,320,5] 13 := by
  apply FastRouting.sound _ _ [34,136,320,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43136 c43136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38518
  · exact u38519
  · exact u38520
  · exact u38521
  · exact u38522
  · exact u38523
  · exact u38524
  · exact u38525
  · exact u38526
  · exact u38527

def r43137 : Route 9 := (fun mask => (mask,id))

def c43137 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43137 : Upper (D 6) (R 6) [34,136,320,6] 13 := by
  apply FastRouting.sound _ _ [34,136,320,6] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43137 c43137
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38528
  · exact u38529
  · exact u38530
  · exact u38531
  · exact u38532
  · exact u38533

def r43138 : Route 9 := (fun mask => (mask,id))

def c43138 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43138 : Upper (D 6) (R 6) [34,136,320,17] 13 := by
  apply FastRouting.sound _ _ [34,136,320,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43138 c43138
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38534
  · exact u38535
  · exact u38536
  · exact u38537
  · exact u38538
  · exact u38539
  · exact u38540
  · exact u38541
  · exact u38542
  · exact u38543

def r43139 : Route 9 := (fun mask => (mask,id))

def c43139 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43139 : Upper (D 6) (R 6) [34,136,320,18] 13 := by
  apply FastRouting.sound _ _ [34,136,320,18] 13 (by decide) (choices 2) [5,33,36,65,68,96] r43139 c43139
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38544
  · exact u38545
  · exact u38546
  · exact u38547
  · exact u38548
  · exact u38549

#print axioms u43139
end Delivery.IrregularNine14.P06
