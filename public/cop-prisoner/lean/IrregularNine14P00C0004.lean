import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0000

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b240 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 23 11 100 296 144 96 209 145 401), lower := (rows 23 11 100 296 144 96 64 128 256), losses := [] }

theorem u240 : Upper (D 0) (R 0) [22,9,96,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b240
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r241 : Route 9 := (fun mask => (mask,id))

def c241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u241 : Upper (D 0) (R 0) [22,9,96,288,128,128] 13 := by
  apply FastRouting.sound _ _ [22,9,96,288,128,128] 13 (by decide) (choices 1) [1,16] r241 c241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2
  · exact u3

def b242 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 292 104 144 33 208 208 464), lower := (rows 23 11 292 104 144 33 64 128 256), losses := [] }

theorem u242 : Upper (D 0) (R 0) [22,9,288,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b242
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r243 : Route 9 := (fun mask => (mask,id))

def c243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u243 : Upper (D 0) (R 0) [22,9,288,96,128,16] 13 := by
  apply FastRouting.sound _ _ [22,9,288,96,128,16] 13 (by decide) (choices 1) [1,128] r243 c243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4
  · exact u5

def b244 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 23 11 292 104 144 96 209 145 401), lower := (rows 23 11 292 104 144 96 64 128 256), losses := [] }

theorem u244 : Upper (D 0) (R 0) [22,9,288,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b244
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r245 : Route 9 := (fun mask => (mask,id))

def c245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u245 : Upper (D 0) (R 0) [22,9,288,96,128,128] 13 := by
  apply FastRouting.sound _ _ [22,9,288,96,128,128] 13 (by decide) (choices 1) [1,16] r245 c245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6
  · exact u7

def b246 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 76 296 144 33 208 208 464), lower := (rows 23 35 76 296 144 33 64 128 256), losses := [] }

theorem u246 : Upper (D 0) (R 0) [22,33,72,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b246
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 76 296 144 48 193 193 449), lower := (rows 23 35 76 296 144 48 64 128 256), losses := [] }

theorem u247 : Upper (D 0) (R 0) [22,33,72,288,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b247
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 23 35 76 296 144 96 209 145 401), lower := (rows 23 35 76 296 144 96 64 128 256), losses := [] }

theorem u248 : Upper (D 0) (R 0) [22,33,72,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b248
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 81, camps := [], pairs := [(1,4)], upper := (rows 23 35 76 296 144 160 81 209 337), lower := (rows 23 35 76 296 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 39 35 76 296 160 160 64 160 256) }] }

theorem u249 : Upper (D 0) (R 0) [22,33,72,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b249
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 268 104 144 33 208 208 464), lower := (rows 23 35 268 104 144 33 64 128 256), losses := [] }

theorem u250 : Upper (D 0) (R 0) [22,33,264,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b250
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 268 104 144 48 193 193 449), lower := (rows 23 35 268 104 144 48 64 128 256), losses := [] }

theorem u251 : Upper (D 0) (R 0) [22,33,264,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b251
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 23 35 268 104 144 96 209 145 401), lower := (rows 23 35 268 104 144 96 64 128 256), losses := [] }

theorem u252 : Upper (D 0) (R 0) [22,33,264,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b252
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 81, camps := [], pairs := [(1,4)], upper := (rows 23 35 268 104 144 160 81 209 337), lower := (rows 23 35 268 104 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 39 35 268 104 160 160 64 160 256) }] }

theorem u253 : Upper (D 0) (R 0) [22,33,264,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b253
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 56 144 33 200 200 456), lower := (rows 23 35 324 56 144 33 64 128 256), losses := [] }

theorem u254 : Upper (D 0) (R 0) [22,33,320,48,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b254
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b255 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 23 35 324 56 144 40 193 193 449), lower := (rows 23 35 324 56 144 40 64 128 256), losses := [] }

theorem u255 : Upper (D 0) (R 0) [22,33,320,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b255
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b256 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 23 35 324 56 144 96 201 137 393), lower := (rows 23 35 324 56 144 96 64 128 256), losses := [] }

theorem u256 : Upper (D 0) (R 0) [22,33,320,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b256
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 23 35 324 56 144 160 73 201 329), lower := (rows 23 35 324 56 144 160 64 128 256), losses := [] }

theorem u257 : Upper (D 0) (R 0) [22,33,320,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b257
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b258 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 324 88 144 33 232 168 424), lower := (rows 23 35 324 88 144 33 64 128 256), losses := [] }

theorem u258 : Upper (D 0) (R 0) [22,33,320,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b258
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 23 35 324 88 144 40 225 161 417), lower := (rows 23 35 324 88 144 40 64 128 256), losses := [] }

theorem u259 : Upper (D 0) (R 0) [22,33,320,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b259
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 41, camps := [], pairs := [(1,4)], upper := (rows 23 35 324 88 144 160 105 169 297), lower := (rows 23 35 324 88 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 39 35 324 104 160 160 64 160 256) }] }

theorem u260 : Upper (D 0) (R 0) [22,33,320,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b260
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 324 104 144 33 216 152 408), lower := (rows 23 35 324 104 144 33 64 128 256), losses := [] }

theorem u261 : Upper (D 0) (R 0) [22,33,320,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b261
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 23 35 324 104 144 40 209 145 401), lower := (rows 23 35 324 104 144 40 64 128 256), losses := [] }

theorem u262 : Upper (D 0) (R 0) [22,33,320,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b262
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 104 144 48 201 137 393), lower := (rows 23 35 324 104 144 48 64 128 256), losses := [] }

theorem u263 : Upper (D 0) (R 0) [22,33,320,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b263
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 25, camps := [], pairs := [(1,4)], upper := (rows 23 35 324 104 144 160 89 153 281), lower := (rows 23 35 324 104 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 39 35 324 104 160 160 64 160 256) }] }

theorem u264 : Upper (D 0) (R 0) [22,33,320,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b264
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 324 168 144 33 88 216 344), lower := (rows 23 35 324 168 144 33 64 128 256), losses := [] }

theorem u265 : Upper (D 0) (R 0) [22,33,320,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b265
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 23 35 324 168 144 40 81 209 337), lower := (rows 23 35 324 168 144 40 64 128 256), losses := [] }

theorem u266 : Upper (D 0) (R 0) [22,33,320,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b266
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 168 144 48 73 201 329), lower := (rows 23 35 324 168 144 48 64 128 256), losses := [] }

theorem u267 : Upper (D 0) (R 0) [22,33,320,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b267
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 23 35 324 168 144 96 89 153 281), lower := (rows 23 35 324 168 144 96 64 128 256), losses := [] }

theorem u268 : Upper (D 0) (R 0) [22,33,320,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b268
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 324 200 144 33 120 184 312), lower := (rows 23 35 324 200 144 33 64 128 256), losses := [] }

theorem u269 : Upper (D 0) (R 0) [22,33,320,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b269
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 23 35 324 200 144 40 113 177 305), lower := (rows 23 35 324 200 144 40 64 128 256), losses := [] }

theorem u270 : Upper (D 0) (R 0) [22,33,320,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b270
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 200 144 48 105 169 297), lower := (rows 23 35 324 200 144 48 64 128 256), losses := [] }

theorem u271 : Upper (D 0) (R 0) [22,33,320,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b271
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r272 : Route 9 := (fun mask => (mask,id))

def c272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u272 : Upper (D 0) (R 0) [22,40,192,320,1,1] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320,1,1] 13 (by decide) (choices 1) [16,32,128] r272 c272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8
  · exact u9
  · exact u10

def r273 : Route 9 := (fun mask => (mask,id))

def c273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u273 : Upper (D 0) (R 0) [22,40,192,320,1,16] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320,1,16] 13 (by decide) (choices 1) [1,32,128] r273 c273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11
  · exact u12
  · exact u13

def r274 : Route 9 := (fun mask => (mask,id))

def c274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u274 : Upper (D 0) (R 0) [22,40,192,320,1,128] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320,1,128] 13 (by decide) (choices 1) [1,16,32] r274 c274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14
  · exact u15
  · exact u16

def r275 : Route 9 := (fun mask => (mask,id))

def c275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u275 : Upper (D 0) (R 0) [22,40,320,192,1,1] 13 := by
  apply FastRouting.sound _ _ [22,40,320,192,1,1] 13 (by decide) (choices 1) [16,32,128] r275 c275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17
  · exact u18
  · exact u19

def r276 : Route 9 := (fun mask => (mask,id))

def c276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u276 : Upper (D 0) (R 0) [22,40,320,192,1,16] 13 := by
  apply FastRouting.sound _ _ [22,40,320,192,1,16] 13 (by decide) (choices 1) [1,32,128] r276 c276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20
  · exact u21
  · exact u22

def b277 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 324 200 17 160 113 177 305), lower := (rows 23 42 324 200 17 160 64 128 256), losses := [] }

theorem u277 : Upper (D 0) (R 0) [22,40,320,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b277
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 23 98 261 56 144 33 200 200 456), lower := (rows 23 98 261 56 144 33 64 128 256), losses := [] }

theorem u278 : Upper (D 0) (R 0) [22,96,257,48,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b278
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 23 98 261 56 144 40 193 193 449), lower := (rows 23 98 261 56 144 40 64 128 256), losses := [] }

theorem u279 : Upper (D 0) (R 0) [22,96,257,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b279
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 261 56 144 96 201 137 393), lower := (rows 23 98 261 56 144 96 64 128 256), losses := [] }

theorem u280 : Upper (D 0) (R 0) [22,96,257,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b280
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 23 98 261 56 144 160 73 201 329), lower := (rows 23 98 261 56 144 160 64 128 256), losses := [] }

theorem u281 : Upper (D 0) (R 0) [22,96,257,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b281
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 88, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 23 98 261 168 144 33 88 216 344), lower := (rows 23 98 261 168 144 33 64 128 256), losses := [] }

theorem u282 : Upper (D 0) (R 0) [22,96,257,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b282
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 23 98 261 168 144 40 81 209 337), lower := (rows 23 98 261 168 144 40 64 128 256), losses := [] }

theorem u283 : Upper (D 0) (R 0) [22,96,257,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b283
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 23 98 261 168 144 48 73 201 329), lower := (rows 23 98 261 168 144 48 64 128 256), losses := [] }

theorem u284 : Upper (D 0) (R 0) [22,96,257,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b284
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 261 168 144 96 89 153 281), lower := (rows 23 98 261 168 144 96 64 128 256), losses := [] }

theorem u285 : Upper (D 0) (R 0) [22,96,257,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b285
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 208, camps := [], pairs := [(1,0)], upper := (rows 23 98 268 168 17 33 208 208 464), lower := (rows 23 98 268 168 17 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 36 40 16 32 81 145 273), good := (rows 470 110 268 174 464 494 64 128 256) }] }

theorem u286 : Upper (D 0) (R 0) [22,96,264,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b286
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 193, camps := [], pairs := [(1,4)], upper := (rows 23 98 268 168 17 48 193 193 449), lower := (rows 23 98 268 168 17 48 64 128 256), losses := [{ target := 4, region := (rows 1 34 36 40 0 32 81 145 273), good := (rows 455 110 268 174 449 494 64 128 256) }] }

theorem u287 : Upper (D 0) (R 0) [22,96,264,160,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b287
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 268 168 17 96 209 145 401), lower := (rows 23 98 268 168 17 96 64 128 256), losses := [] }

theorem u288 : Upper (D 0) (R 0) [22,96,264,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b288
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 23 98 268 168 17 160 81 209 337), lower := (rows 23 98 268 168 17 160 64 128 256), losses := [] }

theorem u289 : Upper (D 0) (R 0) [22,96,264,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b289
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 23 98 388 56 17 33 200 200 456), lower := (rows 23 98 388 56 17 33 64 128 256), losses := [] }

theorem u290 : Upper (D 0) (R 0) [22,96,384,48,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b290
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 23 98 388 56 17 40 193 193 449), lower := (rows 23 98 388 56 17 40 64 128 256), losses := [] }

theorem u291 : Upper (D 0) (R 0) [22,96,384,48,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b291
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 388 56 17 96 201 137 393), lower := (rows 23 98 388 56 17 96 64 128 256), losses := [] }

theorem u292 : Upper (D 0) (R 0) [22,96,384,48,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b292
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 73, camps := [], pairs := [(3,0)], upper := (rows 23 98 388 56 17 160 73 201 329), lower := (rows 23 98 388 56 17 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 16 164 64 128 256), good := (rows 62 98 420 56 24 160 64 160 256) }] }

theorem u293 : Upper (D 0) (R 0) [22,96,384,48,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b293
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 104, camps := [], pairs := [(1,4)], upper := (rows 23 98 388 152 17 33 104 232 360), lower := (rows 23 98 388 152 17 33 64 128 256), losses := [{ target := 4, region := (rows 1 10 12 8 0 49 72 136 264), good := (rows 39 98 388 494 33 33 64 128 256) }] }

theorem u294 : Upper (D 0) (R 0) [22,96,384,144,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b294
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 23 98 388 152 17 40 97 225 353), lower := (rows 23 98 388 152 17 40 64 128 256), losses := [] }

theorem u295 : Upper (D 0) (R 0) [22,96,384,144,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b295
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 388 152 17 96 105 169 297), lower := (rows 23 98 388 152 17 96 64 128 256), losses := [] }

theorem u296 : Upper (D 0) (R 0) [22,96,384,144,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b296
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 88, camps := [], pairs := [(2,5)], upper := (rows 23 98 388 168 17 33 88 216 344), lower := (rows 23 98 388 168 17 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 49 0 72 136 264), good := (rows 23 82 388 476 17 17 64 128 256) }] }

theorem u297 : Upper (D 0) (R 0) [22,96,384,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b297
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 23 98 388 168 17 40 81 209 337), lower := (rows 23 98 388 168 17 40 64 128 256), losses := [] }

theorem u298 : Upper (D 0) (R 0) [22,96,384,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b298
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r299 : Route 9 := (fun mask => (mask,id))

def c299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u299 : Upper (D 0) (R 0) [22,96,384,160,1,16] 13 := by
  apply FastRouting.sound _ _ [22,96,384,160,1,16] 13 (by decide) (choices 1) [1,8] r299 c299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23
  · exact u24

#print axioms u299
end Delivery.IrregularNine14.P00
