import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0452
import IrregularNine14P06C0453
import IrregularNine14P06C0454

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40260 : Route 9 := (fun mask => (mask,id))

def c40260 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40260 : Upper (D 6) (R 6) [96,129,257,18,36] 13 := by
  apply FastRouting.sound _ _ [96,129,257,18,36] 13 (by decide) (choices 1) [2,4,8,64] r40260 c40260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27174
  · exact u27175
  · exact u27176
  · exact u27177

def r40261 : Route 9 := (fun mask => (mask,id))

def c40261 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40261 : Upper (D 6) (R 6) [96,129,257,18,40] 13 := by
  apply FastRouting.sound _ _ [96,129,257,18,40] 13 (by decide) (choices 1) [2,4,64] r40261 c40261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27178
  · exact u27179
  · exact u27180

def b40262 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 131 261 26 112 46 78 142 270), lower := (rows 97 131 261 26 112 32 64 128 256), losses := [] }

theorem u40262 : Upper (D 6) (R 6) [96,129,257,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40263 : Route 9 := (fun mask => (mask,id))

def c40263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40263 : Upper (D 6) (R 6) [96,129,257,34,66] 13 := by
  apply FastRouting.sound _ _ [96,129,257,34,66] 13 (by decide) (choices 1) [4,8,16] r40263 c40263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27181
  · exact u27182
  · exact u27183

def r40264 : Route 9 := (fun mask => (mask,id))

def c40264 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40264 : Upper (D 6) (R 6) [96,129,257,34,68] 13 := by
  apply FastRouting.sound _ _ [96,129,257,34,68] 13 (by decide) (choices 1) [2,4,8,16] r40264 c40264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27184
  · exact u27185
  · exact u27186
  · exact u27187

def r40265 : Route 9 := (fun mask => (mask,id))

def c40265 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40265 : Upper (D 6) (R 6) [96,129,257,34,72] 13 := by
  apply FastRouting.sound _ _ [96,129,257,34,72] 13 (by decide) (choices 1) [2,4,16] r40265 c40265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27188
  · exact u27189
  · exact u27190

def b40266 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 131 261 56 88 38 70 134 262), lower := (rows 97 131 261 56 88 32 64 128 256), losses := [] }

theorem u40266 : Upper (D 6) (R 6) [96,129,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40267 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 262 11 28 116 116 244 372), lower := (rows 97 131 262 11 28 32 64 128 256), losses := [] }

theorem u40267 : Upper (D 6) (R 6) [96,129,258,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40268 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 262 11 52 124 92 220 348), lower := (rows 97 131 262 11 52 32 64 128 256), losses := [] }

theorem u40268 : Upper (D 6) (R 6) [96,129,258,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40269 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 262 11 56 116 84 212 340), lower := (rows 97 131 262 11 56 32 64 128 256), losses := [] }

theorem u40269 : Upper (D 6) (R 6) [96,129,258,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40270 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 131 262 13 22 120 120 248 376), lower := (rows 97 131 262 13 22 32 64 128 256), losses := [] }

theorem u40270 : Upper (D 6) (R 6) [96,129,258,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40271 : Route 9 := (fun mask => (mask,id))

def c40271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40271 : Upper (D 6) (R 6) [96,129,258,5,10] 13 := by
  apply FastRouting.sound _ _ [96,129,258,5,10] 13 (by decide) (choices 1) [4,16,64] r40271 c40271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27191
  · exact u27192
  · exact u27193

def b40272 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 97 131 262 13 28 114 114 242 370), lower := (rows 97 131 262 13 28 32 64 128 256), losses := [] }

theorem u40272 : Upper (D 6) (R 6) [96,129,258,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40273 : Route 9 := (fun mask => (mask,id))

def c40273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40273 : Upper (D 6) (R 6) [96,129,258,5,34] 13 := by
  apply FastRouting.sound _ _ [96,129,258,5,34] 13 (by decide) (choices 1) [4,8,16,64] r40273 c40273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27194
  · exact u27195
  · exact u27196
  · exact u27197

def r40274 : Route 9 := (fun mask => (mask,id))

def c40274 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40274 : Upper (D 6) (R 6) [96,129,258,5,36] 13 := by
  apply FastRouting.sound _ _ [96,129,258,5,36] 13 (by decide) (choices 1) [2,8,16,64] r40274 c40274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27198
  · exact u27199
  · exact u27200
  · exact u27201

def r40275 : Route 9 := (fun mask => (mask,id))

def c40275 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40275 : Upper (D 6) (R 6) [96,129,258,5,40] 13 := by
  apply FastRouting.sound _ _ [96,129,258,5,40] 13 (by decide) (choices 1) [2,4,16,64] r40275 c40275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27202
  · exact u27203
  · exact u27204
  · exact u27205

def b40276 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 131 262 13 112 62 94 158 286), lower := (rows 97 131 262 13 112 32 64 128 256), losses := [] }

theorem u40276 : Upper (D 6) (R 6) [96,129,258,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40277 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 131 262 14 25 116 116 244 372), lower := (rows 97 131 262 14 25 32 64 128 256), losses := [] }

theorem u40277 : Upper (D 6) (R 6) [96,129,258,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40278 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 131 262 14 28 113 113 241 369), lower := (rows 97 131 262 14 28 32 64 128 256), losses := [] }

theorem u40278 : Upper (D 6) (R 6) [96,129,258,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40279 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 131 262 14 52 121 89 217 345), lower := (rows 97 131 262 14 52 32 64 128 256), losses := [] }

theorem u40279 : Upper (D 6) (R 6) [96,129,258,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40280 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 131 262 14 56 117 85 213 341), lower := (rows 97 131 262 14 56 32 64 128 256), losses := [] }

theorem u40280 : Upper (D 6) (R 6) [96,129,258,6,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40281 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 262 25 26 100 100 228 356), lower := (rows 97 131 262 25 26 32 64 128 256), losses := [] }

theorem u40281 : Upper (D 6) (R 6) [96,129,258,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40282 : Route 9 := (fun mask => (mask,id))

def c40282 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40282 : Upper (D 6) (R 6) [96,129,258,17,12] 13 := by
  apply FastRouting.sound _ _ [96,129,258,17,12] 13 (by decide) (choices 1) [2,4,64] r40282 c40282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27206
  · exact u27207
  · exact u27208

def r40283 : Route 9 := (fun mask => (mask,id))

def c40283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40283 : Upper (D 6) (R 6) [96,129,258,17,34] 13 := by
  apply FastRouting.sound _ _ [96,129,258,17,34] 13 (by decide) (choices 1) [4,8,64] r40283 c40283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27209
  · exact u27210
  · exact u27211

def r40284 : Route 9 := (fun mask => (mask,id))

def c40284 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40284 : Upper (D 6) (R 6) [96,129,258,17,36] 13 := by
  apply FastRouting.sound _ _ [96,129,258,17,36] 13 (by decide) (choices 1) [2,4,8,64] r40284 c40284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27212
  · exact u27213
  · exact u27214
  · exact u27215

def b40285 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 131 262 25 56 102 70 198 326), lower := (rows 97 131 262 25 56 32 64 128 256), losses := [] }

theorem u40285 : Upper (D 6) (R 6) [96,129,258,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40286 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 131 262 25 112 46 78 142 270), lower := (rows 97 131 262 25 112 32 64 128 256), losses := [] }

theorem u40286 : Upper (D 6) (R 6) [96,129,258,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40287 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 131 262 26 28 101 101 229 357), lower := (rows 97 131 262 26 28 32 64 128 256), losses := [] }

theorem u40287 : Upper (D 6) (R 6) [96,129,258,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40288 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 131 262 26 49 108 76 204 332), lower := (rows 97 131 262 26 49 32 64 128 256), losses := [] }

theorem u40288 : Upper (D 6) (R 6) [96,129,258,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40289 : Route 9 := (fun mask => (mask,id))

def c40289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40289 : Upper (D 6) (R 6) [96,129,258,18,36] 13 := by
  apply FastRouting.sound _ _ [96,129,258,18,36] 13 (by decide) (choices 1) [1,4,8,64] r40289 c40289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27216
  · exact u27217
  · exact u27218
  · exact u27219

def b40290 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 131 262 26 56 101 69 197 325), lower := (rows 97 131 262 26 56 32 64 128 256), losses := [] }

theorem u40290 : Upper (D 6) (R 6) [96,129,258,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40291 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 131 262 26 112 45 77 141 269), lower := (rows 97 131 262 26 112 32 64 128 256), losses := [] }

theorem u40291 : Upper (D 6) (R 6) [96,129,258,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40292 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 131 262 28 28 99 99 227 355), lower := (rows 97 131 262 28 28 32 64 128 256), losses := [] }

theorem u40292 : Upper (D 6) (R 6) [96,129,258,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40293 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 131 262 28 49 110 78 206 334), lower := (rows 97 131 262 28 49 32 64 128 256), losses := [] }

theorem u40293 : Upper (D 6) (R 6) [96,129,258,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40294 : Route 9 := (fun mask => (mask,id))

def c40294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40294 : Upper (D 6) (R 6) [96,129,258,20,34] 13 := by
  apply FastRouting.sound _ _ [96,129,258,20,34] 13 (by decide) (choices 1) [1,4,8,64] r40294 c40294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27220
  · exact u27221
  · exact u27222
  · exact u27223

def b40295 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 131 262 28 52 107 75 203 331), lower := (rows 97 131 262 28 52 32 64 128 256), losses := [] }

theorem u40295 : Upper (D 6) (R 6) [96,129,258,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40296 : Route 9 := (fun mask => (mask,id))

def c40296 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40296 : Upper (D 6) (R 6) [96,129,258,20,40] 13 := by
  apply FastRouting.sound _ _ [96,129,258,20,40] 13 (by decide) (choices 1) [1,2,4,64] r40296 c40296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27224
  · exact u27225
  · exact u27226
  · exact u27227

def b40297 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 131 262 28 112 47 79 143 271), lower := (rows 97 131 262 28 112 32 64 128 256), losses := [] }

theorem u40297 : Upper (D 6) (R 6) [96,129,258,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40298 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 131 262 41 82 60 92 156 284), lower := (rows 97 131 262 41 82 32 64 128 256), losses := [] }

theorem u40298 : Upper (D 6) (R 6) [96,129,258,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40299 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 131 262 41 84 62 94 158 286), lower := (rows 97 131 262 41 84 32 64 128 256), losses := [] }

theorem u40299 : Upper (D 6) (R 6) [96,129,258,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40300 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 131 262 41 88 54 86 150 278), lower := (rows 97 131 262 41 88 32 64 128 256), losses := [] }

theorem u40300 : Upper (D 6) (R 6) [96,129,258,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40301 : Route 9 := (fun mask => (mask,id))

def c40301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40301 : Upper (D 6) (R 6) [96,129,258,34,68] 13 := by
  apply FastRouting.sound _ _ [96,129,258,34,68] 13 (by decide) (choices 1) [1,4,8,16] r40301 c40301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27228
  · exact u27229
  · exact u27230
  · exact u27231

def r40302 : Route 9 := (fun mask => (mask,id))

def c40302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40302 : Upper (D 6) (R 6) [96,129,258,34,72] 13 := by
  apply FastRouting.sound _ _ [96,129,258,34,72] 13 (by decide) (choices 1) [1,4,16] r40302 c40302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27232
  · exact u27233
  · exact u27234

def r40303 : Route 9 := (fun mask => (mask,id))

def c40303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40303 : Upper (D 6) (R 6) [96,129,258,36,68] 13 := by
  apply FastRouting.sound _ _ [96,129,258,36,68] 13 (by decide) (choices 1) [1,2,8,16] r40303 c40303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27235
  · exact u27236
  · exact u27237
  · exact u27238

def r40304 : Route 9 := (fun mask => (mask,id))

def c40304 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40304 : Upper (D 6) (R 6) [96,129,258,36,72] 13 := by
  apply FastRouting.sound _ _ [96,129,258,36,72] 13 (by decide) (choices 1) [1,2,4,16] r40304 c40304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27239
  · exact u27240
  · exact u27241
  · exact u27242

def b40305 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 131 262 56 88 39 71 135 263), lower := (rows 97 131 262 56 88 32 64 128 256), losses := [] }

theorem u40305 : Upper (D 6) (R 6) [96,129,258,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40306 : Route 9 := (fun mask => (mask,id))

def c40306 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40306 : Upper (D 6) (R 6) [96,129,264,5,6] 13 := by
  apply FastRouting.sound _ _ [96,129,264,5,6] 13 (by decide) (choices 1) [2,16,64] r40306 c40306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27243
  · exact u27244
  · exact u27245

def r40307 : Route 9 := (fun mask => (mask,id))

def c40307 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40307 : Upper (D 6) (R 6) [96,129,264,5,34] 13 := by
  apply FastRouting.sound _ _ [96,129,264,5,34] 13 (by decide) (choices 1) [2,4,16,64] r40307 c40307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27246
  · exact u27247
  · exact u27248
  · exact u27249

def r40308 : Route 9 := (fun mask => (mask,id))

def c40308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40308 : Upper (D 6) (R 6) [96,129,264,5,36] 13 := by
  apply FastRouting.sound _ _ [96,129,264,5,36] 13 (by decide) (choices 1) [2,16,64] r40308 c40308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27250
  · exact u27251
  · exact u27252

def b40309 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 131 268 13 112 54 86 150 278), lower := (rows 97 131 268 13 112 32 64 128 256), losses := [] }

theorem u40309 : Upper (D 6) (R 6) [96,129,264,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40310 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 131 268 14 19 116 116 244 372), lower := (rows 97 131 268 14 19 32 64 128 256), losses := [] }

theorem u40310 : Upper (D 6) (R 6) [96,129,264,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40311 : Route 9 := (fun mask => (mask,id))

def c40311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40311 : Upper (D 6) (R 6) [96,129,264,6,5] 13 := by
  apply FastRouting.sound _ _ [96,129,264,6,5] 13 (by decide) (choices 1) [2,16,64] r40311 c40311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27253
  · exact u27254
  · exact u27255

def b40312 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 131 268 14 22 113 113 241 369), lower := (rows 97 131 268 14 22 32 64 128 256), losses := [] }

theorem u40312 : Upper (D 6) (R 6) [96,129,264,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40313 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 131 268 14 49 118 86 214 342), lower := (rows 97 131 268 14 49 32 64 128 256), losses := [] }

theorem u40313 : Upper (D 6) (R 6) [96,129,264,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40314 : Route 9 := (fun mask => (mask,id))

def c40314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40314 : Upper (D 6) (R 6) [96,129,264,6,34] 13 := by
  apply FastRouting.sound _ _ [96,129,264,6,34] 13 (by decide) (choices 1) [1,4,16,64] r40314 c40314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27256
  · exact u27257
  · exact u27258
  · exact u27259

def r40315 : Route 9 := (fun mask => (mask,id))

def c40315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40315 : Upper (D 6) (R 6) [96,129,264,6,36] 13 := by
  apply FastRouting.sound _ _ [96,129,264,6,36] 13 (by decide) (choices 1) [1,2,16,64] r40315 c40315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27260
  · exact u27261
  · exact u27262
  · exact u27263

def b40316 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 131 268 14 112 55 87 151 279), lower := (rows 97 131 268 14 112 32 64 128 256), losses := [] }

theorem u40316 : Upper (D 6) (R 6) [96,129,264,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40317 : Route 9 := (fun mask => (mask,id))

def c40317 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40317 : Upper (D 6) (R 6) [96,129,264,17,6] 13 := by
  apply FastRouting.sound _ _ [96,129,264,17,6] 13 (by decide) (choices 1) [2,4,64] r40317 c40317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27264
  · exact u27265
  · exact u27266

def r40318 : Route 9 := (fun mask => (mask,id))

def c40318 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40318 : Upper (D 6) (R 6) [96,129,264,17,34] 13 := by
  apply FastRouting.sound _ _ [96,129,264,17,34] 13 (by decide) (choices 1) [2,4,64] r40318 c40318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27267
  · exact u27268
  · exact u27269

def r40319 : Route 9 := (fun mask => (mask,id))

def c40319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40319 : Upper (D 6) (R 6) [96,129,264,17,36] 13 := by
  apply FastRouting.sound _ _ [96,129,264,17,36] 13 (by decide) (choices 1) [2,4,64] r40319 c40319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27270
  · exact u27271
  · exact u27272

#print axioms u40319
end Delivery.IrregularNine14.P06
