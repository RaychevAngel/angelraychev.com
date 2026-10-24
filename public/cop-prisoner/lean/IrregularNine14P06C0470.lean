import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0155

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28200 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 26 164 42 273 101 69 197 325), lower := (rows 7 26 164 42 273 32 64 128 256), losses := [] }

theorem u28200 : Upper (D 6) (R 6) [6,24,160,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28200
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28201 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 104, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 164 42 276 97 65 193 321), lower := (rows 7 26 164 42 276 32 64 128 256), losses := [] }

theorem u28201 : Upper (D 6) (R 6) [6,24,160,34,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28201
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28202 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 26 164 42 336 101 69 197 325), lower := (rows 7 26 164 42 336 32 64 128 256), losses := [] }

theorem u28202 : Upper (D 6) (R 6) [6,24,160,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28202
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28203 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 164 44 81 355 323 451 323), lower := (rows 7 26 164 44 81 32 64 128 256), losses := [] }

theorem u28203 : Upper (D 6) (R 6) [6,24,160,36,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28203
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28204 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 164 44 82 353 321 449 321), lower := (rows 7 26 164 44 82 32 64 128 256), losses := [] }

theorem u28204 : Upper (D 6) (R 6) [6,24,160,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28204
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28205 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 164 44 273 99 67 195 323), lower := (rows 7 26 164 44 273 32 64 128 256), losses := [] }

theorem u28205 : Upper (D 6) (R 6) [6,24,160,36,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28205
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28206 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 164 44 274 97 65 193 321), lower := (rows 7 26 164 44 274 32 64 128 256), losses := [] }

theorem u28206 : Upper (D 6) (R 6) [6,24,160,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28206
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28207 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 164 44 336 99 67 195 323), lower := (rows 7 26 164 44 336 32 64 128 256), losses := [] }

theorem u28207 : Upper (D 6) (R 6) [6,24,160,36,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28207
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28208 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 7 26 164 73 81 294 358 422 294), lower := (rows 7 26 164 73 81 32 64 128 256), losses := [] }

theorem u28208 : Upper (D 6) (R 6) [6,24,160,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28208
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28209 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 7 26 164 73 82 293 357 421 293), lower := (rows 7 26 164 73 82 32 64 128 256), losses := [] }

theorem u28209 : Upper (D 6) (R 6) [6,24,160,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28209
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28210 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 11, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 26 164 73 84 291 355 419 291), lower := (rows 7 26 164 73 84 32 64 128 256), losses := [] }

theorem u28210 : Upper (D 6) (R 6) [6,24,160,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28210
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28211 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 328, targets := 32 }], pairs := [(0,6),(2,6),(3,5)], upper := (rows 7 26 164 73 112 295 327 391 263), lower := (rows 7 26 164 73 112 32 64 128 256), losses := [] }

theorem u28211 : Upper (D 6) (R 6) [6,24,160,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28211
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28212 : Route 9 := (fun mask => (mask,id))

def c28212 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28212 : Upper (D 6) (R 6) [6,24,160,65,257] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,257] 13 (by decide) (choices 1) [2,4,64] r28212 c28212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9302
  · exact u9303
  · exact u9304

def r28213 : Route 9 := (fun mask => (mask,id))

def c28213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28213 : Upper (D 6) (R 6) [6,24,160,65,258] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,258] 13 (by decide) (choices 1) [1,4,64] r28213 c28213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9305
  · exact u9306
  · exact u9307

def r28214 : Route 9 := (fun mask => (mask,id))

def c28214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28214 : Upper (D 6) (R 6) [6,24,160,65,260] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,260] 13 (by decide) (choices 1) [1,2,64] r28214 c28214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9308
  · exact u9309
  · exact u9310

def r28215 : Route 9 := (fun mask => (mask,id))

def c28215 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28215 : Upper (D 6) (R 6) [6,24,160,65,288] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,288] 13 (by decide) (choices 1) [1,2,4,64] r28215 c28215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9311
  · exact u9312
  · exact u9313
  · exact u9314

def r28216 : Route 9 := (fun mask => (mask,id))

def c28216 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28216 : Upper (D 6) (R 6) [6,24,160,65,320] 13 := by
  apply FastRouting.sound _ _ [6,24,160,65,320] 13 (by decide) (choices 1) [1,2,4] r28216 c28216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9315
  · exact u9316
  · exact u9317

def b28217 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 26 164 74 84 289 353 417 289), lower := (rows 7 26 164 74 84 32 64 128 256), losses := [] }

theorem u28217 : Upper (D 6) (R 6) [6,24,160,66,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28217
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28218 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 7 26 164 74 112 293 325 389 261), lower := (rows 7 26 164 74 112 32 64 128 256), losses := [] }

theorem u28218 : Upper (D 6) (R 6) [6,24,160,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28218
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28219 : Route 9 := (fun mask => (mask,id))

def c28219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28219 : Upper (D 6) (R 6) [6,24,160,66,257] 13 := by
  apply FastRouting.sound _ _ [6,24,160,66,257] 13 (by decide) (choices 1) [1,4,64] r28219 c28219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9318
  · exact u9319
  · exact u9320

def b28220 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 104, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 164 74 276 97 97 225 353), lower := (rows 7 26 164 74 276 32 64 128 256), losses := [] }

theorem u28220 : Upper (D 6) (R 6) [6,24,160,66,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28220
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28221 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 164 74 304 101 69 197 325), lower := (rows 7 26 164 74 304 32 64 128 256), losses := [] }

theorem u28221 : Upper (D 6) (R 6) [6,24,160,66,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28221
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28222 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 7 26 164 74 336 37 101 165 293), lower := (rows 7 26 164 74 336 32 64 128 256), losses := [] }

theorem u28222 : Upper (D 6) (R 6) [6,24,160,66,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28222
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28223 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 26 164 76 112 291 323 387 259), lower := (rows 7 26 164 76 112 32 64 128 256), losses := [] }

theorem u28223 : Upper (D 6) (R 6) [6,24,160,68,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28223
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28224 : Route 9 := (fun mask => (mask,id))

def c28224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28224 : Upper (D 6) (R 6) [6,24,160,68,257] 13 := by
  apply FastRouting.sound _ _ [6,24,160,68,257] 13 (by decide) (choices 1) [1,2,64] r28224 c28224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9321
  · exact u9322
  · exact u9323

def b28225 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 7 26 164 76 274 97 97 225 353), lower := (rows 7 26 164 76 274 32 64 128 256), losses := [] }

theorem u28225 : Upper (D 6) (R 6) [6,24,160,68,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28225
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28226 : Route 9 := (fun mask => (mask,id))

def c28226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28226 : Upper (D 6) (R 6) [6,24,160,68,288] 13 := by
  apply FastRouting.sound _ _ [6,24,160,68,288] 13 (by decide) (choices 1) [1,2,64] r28226 c28226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9324
  · exact u9325
  · exact u9326

def b28227 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 26 164 76 336 35 99 163 291), lower := (rows 7 26 164 76 336 32 64 128 256), losses := [] }

theorem u28227 : Upper (D 6) (R 6) [6,24,160,68,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28227
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28228 : Route 9 := (fun mask => (mask,id))

def c28228 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28228 : Upper (D 6) (R 6) [6,24,160,96,257] 13 := by
  apply FastRouting.sound _ _ [6,24,160,96,257] 13 (by decide) (choices 1) [1,2,4,64] r28228 c28228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9327
  · exact u9328
  · exact u9329
  · exact u9330

def b28229 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 26 164 104 274 101 69 197 325), lower := (rows 7 26 164 104 274 32 64 128 256), losses := [] }

theorem u28229 : Upper (D 6) (R 6) [6,24,160,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28229
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28230 : Route 9 := (fun mask => (mask,id))

def c28230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28230 : Upper (D 6) (R 6) [6,24,160,96,260] 13 := by
  apply FastRouting.sound _ _ [6,24,160,96,260] 13 (by decide) (choices 1) [1,2,64] r28230 c28230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9331
  · exact u9332
  · exact u9333

def b28231 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,6),(2,6),(4,5)], upper := (rows 7 26 164 104 336 39 71 135 263), lower := (rows 7 26 164 104 336 32 64 128 256), losses := [] }

theorem u28231 : Upper (D 6) (R 6) [6,24,160,96,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28231
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28232 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 26 388 11 49 100 100 228 356), lower := (rows 7 26 388 11 49 32 64 128 256), losses := [] }

theorem u28232 : Upper (D 6) (R 6) [6,24,384,3,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28232
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28233 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 388 11 52 97 97 225 353), lower := (rows 7 26 388 11 52 32 64 128 256), losses := [] }

theorem u28233 : Upper (D 6) (R 6) [6,24,384,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28233
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28234 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 26 388 11 112 101 101 229 357), lower := (rows 7 26 388 11 112 32 64 128 256), losses := [] }

theorem u28234 : Upper (D 6) (R 6) [6,24,384,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28234
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28235 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 26 388 13 49 98 98 226 354), lower := (rows 7 26 388 13 49 32 64 128 256), losses := [] }

theorem u28235 : Upper (D 6) (R 6) [6,24,384,5,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28235
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28236 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 7 26 388 13 50 97 97 225 353), lower := (rows 7 26 388 13 50 32 64 128 256), losses := [] }

theorem u28236 : Upper (D 6) (R 6) [6,24,384,5,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28236
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28237 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 26 388 13 112 99 99 227 355), lower := (rows 7 26 388 13 112 32 64 128 256), losses := [] }

theorem u28237 : Upper (D 6) (R 6) [6,24,384,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28237
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28238 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 388 14 49 97 97 225 353), lower := (rows 7 26 388 14 49 32 64 128 256), losses := [] }

theorem u28238 : Upper (D 6) (R 6) [6,24,384,6,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28238
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28239 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 388 14 112 97 97 225 353), lower := (rows 7 26 388 14 112 32 64 128 256), losses := [] }

theorem u28239 : Upper (D 6) (R 6) [6,24,384,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28239
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28240 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 18, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 7 26 388 41 49 102 70 198 326), lower := (rows 7 26 388 41 49 32 64 128 256), losses := [] }

theorem u28240 : Upper (D 6) (R 6) [6,24,384,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28240
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28241 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 26 388 41 50 101 69 197 325), lower := (rows 7 26 388 41 50 32 64 128 256), losses := [] }

theorem u28241 : Upper (D 6) (R 6) [6,24,384,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28241
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28242 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 388 41 52 99 67 195 323), lower := (rows 7 26 388 41 52 32 64 128 256), losses := [] }

theorem u28242 : Upper (D 6) (R 6) [6,24,384,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28242
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28243 : Route 9 := (fun mask => (mask,id))

def c28243 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28243 : Upper (D 6) (R 6) [6,24,384,33,65] 13 := by
  apply FastRouting.sound _ _ [6,24,384,33,65] 13 (by decide) (choices 1) [2,4,64] r28243 c28243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9334
  · exact u9335
  · exact u9336

def r28244 : Route 9 := (fun mask => (mask,id))

def c28244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28244 : Upper (D 6) (R 6) [6,24,384,33,66] 13 := by
  apply FastRouting.sound _ _ [6,24,384,33,66] 13 (by decide) (choices 1) [1,4,64] r28244 c28244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9337
  · exact u9338
  · exact u9339

def r28245 : Route 9 := (fun mask => (mask,id))

def c28245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28245 : Upper (D 6) (R 6) [6,24,384,33,68] 13 := by
  apply FastRouting.sound _ _ [6,24,384,33,68] 13 (by decide) (choices 1) [1,2,64] r28245 c28245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9340
  · exact u9341
  · exact u9342

def r28246 : Route 9 := (fun mask => (mask,id))

def c28246 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28246 : Upper (D 6) (R 6) [6,24,384,33,96] 13 := by
  apply FastRouting.sound _ _ [6,24,384,33,96] 13 (by decide) (choices 1) [1,2,4,64] r28246 c28246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9343
  · exact u9344
  · exact u9345
  · exact u9346

def b28247 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 26 388 42 52 97 65 193 321), lower := (rows 7 26 388 42 52 32 64 128 256), losses := [] }

theorem u28247 : Upper (D 6) (R 6) [6,24,384,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28247
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28248 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 104, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 388 42 84 97 97 225 353), lower := (rows 7 26 388 42 84 32 64 128 256), losses := [] }

theorem u28248 : Upper (D 6) (R 6) [6,24,384,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28248
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28249 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 26 388 42 112 101 69 197 325), lower := (rows 7 26 388 42 112 32 64 128 256), losses := [] }

theorem u28249 : Upper (D 6) (R 6) [6,24,384,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28249
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28250 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(2,5),(4,2)], upper := (rows 7 26 388 44 112 99 67 195 323), lower := (rows 7 26 388 44 112 32 64 128 256), losses := [] }

theorem u28250 : Upper (D 6) (R 6) [6,24,384,36,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28250
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28251 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 388 104 112 39 71 135 263), lower := (rows 7 26 388 104 112 32 64 128 256), losses := [] }

theorem u28251 : Upper (D 6) (R 6) [6,24,384,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28251
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28252 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 496, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 69 14 56 496 464 464 464), lower := (rows 7 35 69 14 56 32 64 128 256), losses := [] }

theorem u28252 : Upper (D 6) (R 6) [6,33,65,6,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28252
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28253 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 496, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 69 14 112 440 472 408 408), lower := (rows 7 35 69 14 112 32 64 128 256), losses := [] }

theorem u28253 : Upper (D 6) (R 6) [6,33,65,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28253
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28254 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 496, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 69 14 152 368 368 496 368), lower := (rows 7 35 69 14 152 32 64 128 256), losses := [] }

theorem u28254 : Upper (D 6) (R 6) [6,33,65,6,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28254
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28255 : PairBound 9 := { available := 344, camps := [{ cop := 3, region := 496, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 69 14 176 376 344 472 344), lower := (rows 7 35 69 14 176 32 64 128 256), losses := [] }

theorem u28255 : Upper (D 6) (R 6) [6,33,65,6,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28255
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28256 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 496, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 69 14 400 120 120 248 376), lower := (rows 7 35 69 14 400 32 64 128 256), losses := [] }

theorem u28256 : Upper (D 6) (R 6) [6,33,65,6,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28256
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28257 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 69 26 28 480 480 480 480), lower := (rows 7 35 69 26 28 32 64 128 256), losses := [] }

theorem u28257 : Upper (D 6) (R 6) [6,33,65,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28257
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28258 : PairBound 9 := { available := 456, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 69 26 52 488 456 456 456), lower := (rows 7 35 69 26 52 32 64 128 256), losses := [] }

theorem u28258 : Upper (D 6) (R 6) [6,33,65,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28258
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28259 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 24, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 69 26 56 484 452 452 452), lower := (rows 7 35 69 26 56 32 64 128 256), losses := [] }

theorem u28259 : Upper (D 6) (R 6) [6,33,65,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28259
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28259
end Delivery.IrregularNine14.P06
