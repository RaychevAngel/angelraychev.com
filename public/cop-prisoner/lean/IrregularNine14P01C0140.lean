import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0087
import IrregularNine14P01C0088
import IrregularNine14P01C0089

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8400 : Route 9 := (fun mask => (mask,id))

def c8400 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8400 : Upper (D 1) (R 1) [304,12,65,130] 13 := by
  apply FastRouting.sound _ _ [304,12,65,130] 13 (by decide) (choices 1) [2,32,64,128] r8400 c8400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5255
  · exact u5256
  · exact u5257
  · exact u5258

def r8401 : Route 9 := (fun mask => (mask,id))

def c8401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8401 : Upper (D 1) (R 1) [304,12,65,144] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144] 13 (by decide) (choices 1) [2,32,64,128] r8401 c8401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5259
  · exact u5260
  · exact u5261
  · exact u5262

def b8402 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 69 200 178 178 242 178 434), lower := (rows 305 14 69 200 16 32 64 128 256), losses := [] }

theorem u8402 : Upper (D 1) (R 1) [304,12,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8402
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8403 : PairBound 9 := { available := 177, camps := [{ cop := 6, region := 14, targets := 16 }], pairs := [(1,4)], upper := (rows 305 14 70 74 177 177 241 177 433), lower := (rows 305 14 70 74 16 32 64 128 256), losses := [] }

theorem u8403 : Upper (D 1) (R 1) [304,12,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8403
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8404 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 14 70 88 179 163 227 163 419), lower := (rows 305 14 70 88 16 32 64 128 256), losses := [] }

theorem u8404 : Upper (D 1) (R 1) [304,12,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8404
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8405 : PairBound 9 := { available := 241, camps := [{ cop := 1, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 70 138 241 241 241 241 497), lower := (rows 305 14 70 138 16 32 64 128 256), losses := [] }

theorem u8405 : Upper (D 1) (R 1) [304,12,66,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8405
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8406 : Route 9 := (fun mask => (mask,id))

def c8406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8406 : Upper (D 1) (R 1) [304,12,66,144] 13 := by
  apply FastRouting.sound _ _ [304,12,66,144] 13 (by decide) (choices 1) [1,2,32,64,128] r8406 c8406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5263
  · exact u5264
  · exact u5265
  · exact u5266
  · exact u5267

def b8407 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 14 70 200 179 179 243 179 435), lower := (rows 305 14 70 200 16 32 64 128 256), losses := [] }

theorem u8407 : Upper (D 1) (R 1) [304,12,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8407
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8408 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 84 104 147 163 195 131 387), lower := (rows 305 14 84 104 16 32 64 128 256), losses := [] }

theorem u8408 : Upper (D 1) (R 1) [304,12,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8408
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8409 : Route 9 := (fun mask => (mask,id))

def c8409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8409 : Upper (D 1) (R 1) [304,12,80,160] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160] 13 (by decide) (choices 1) [1,2,64,128] r8409 c8409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5268
  · exact u5269
  · exact u5270
  · exact u5271

def b8410 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 84 200 179 163 227 163 419), lower := (rows 305 14 84 200 16 32 64 128 256), losses := [] }

theorem u8410 : Upper (D 1) (R 1) [304,12,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8410
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8411 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 305 14 196 200 51 51 115 179 307), lower := (rows 305 14 196 200 16 32 64 128 256), losses := [] }

theorem u8411 : Upper (D 1) (R 1) [304,12,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8411
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8412 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 14 11 240 224 224 224 480), lower := (rows 305 22 14 11 16 32 64 128 256), losses := [] }

theorem u8412 : Upper (D 1) (R 1) [304,20,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8412
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8413 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 305 22 14 41 210 226 194 194 450), lower := (rows 305 22 14 41 16 32 64 128 256), losses := [] }

theorem u8413 : Upper (D 1) (R 1) [304,20,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8413
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8414 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 305 22 14 42 209 225 193 193 449), lower := (rows 305 22 14 42 16 32 64 128 256), losses := [] }

theorem u8414 : Upper (D 1) (R 1) [304,20,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8414
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8415 : Route 9 := (fun mask => (mask,id))

def c8415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8415 : Upper (D 1) (R 1) [304,20,10,65] 13 := by
  apply FastRouting.sound _ _ [304,20,10,65] 13 (by decide) (choices 1) [2,32,64,128] r8415 c8415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5272
  · exact u5273
  · exact u5274
  · exact u5275

def b8416 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 22 14 74 241 225 225 225 481), lower := (rows 305 22 14 74 16 32 64 128 256), losses := [] }

theorem u8416 : Upper (D 1) (R 1) [304,20,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8416
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8417 : Route 9 := (fun mask => (mask,id))

def c8417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8417 : Upper (D 1) (R 1) [304,20,10,96] 13 := by
  apply FastRouting.sound _ _ [304,20,10,96] 13 (by decide) (choices 1) [1,2,64,128] r8417 c8417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5276
  · exact u5277
  · exact u5278
  · exact u5279

def r8418 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8418 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8418 : Upper (D 1) (R 1) [304,20,10,192] 13 := by
  apply FastRouting.sound _ _ [304,20,10,192] 13 (by decide) (choices 1) [1,2,32,64] r8418 c8418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5280
  · exact u5281
  · exact u5282
  · exact u5283

def b8419 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 305 22 44 11 210 226 194 194 450), lower := (rows 305 22 44 11 16 32 64 128 256), losses := [] }

theorem u8419 : Upper (D 1) (R 1) [304,20,40,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8419
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8420 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 44 73 210 226 194 194 450), lower := (rows 305 22 44 73 16 32 64 128 256), losses := [] }

theorem u8420 : Upper (D 1) (R 1) [304,20,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8420
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8421 : Route 9 := (fun mask => (mask,id))

def c8421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8421 : Upper (D 1) (R 1) [304,20,40,66] 13 := by
  apply FastRouting.sound _ _ [304,20,40,66] 13 (by decide) (choices 1) [1,2,64,128] r8421 c8421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5284
  · exact u5285
  · exact u5286
  · exact u5287

def r8422 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8422 : Upper (D 1) (R 1) [304,20,40,192] 13 := by
  apply FastRouting.sound _ _ [304,20,40,192] 13 (by decide) (choices 1) [1,2,64] r8422 c8422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5288
  · exact u5289
  · exact u5290

def b8423 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 70 11 248 232 232 232 488), lower := (rows 305 22 70 11 16 32 64 128 256), losses := [] }

theorem u8423 : Upper (D 1) (R 1) [304,20,66,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8423
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8424 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 22 70 41 218 234 202 202 458), lower := (rows 305 22 70 41 16 32 64 128 256), losses := [] }

theorem u8424 : Upper (D 1) (R 1) [304,20,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8424
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8425 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 70 42 217 233 201 201 457), lower := (rows 305 22 70 42 16 32 64 128 256), losses := [] }

theorem u8425 : Upper (D 1) (R 1) [304,20,66,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8425
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8426 : Route 9 := (fun mask => (mask,id))

def c8426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8426 : Upper (D 1) (R 1) [304,20,66,65] 13 := by
  apply FastRouting.sound _ _ [304,20,66,65] 13 (by decide) (choices 1) [2,8,32,128] r8426 c8426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5291
  · exact u5292
  · exact u5293
  · exact u5294

def b8427 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 70 74 185 169 233 169 425), lower := (rows 305 22 70 74 16 32 64 128 256), losses := [] }

theorem u8427 : Upper (D 1) (R 1) [304,20,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8427
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8428 : Route 9 := (fun mask => (mask,id))

def c8428 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8428 : Upper (D 1) (R 1) [304,20,66,96] 13 := by
  apply FastRouting.sound _ _ [304,20,66,96] 13 (by decide) (choices 1) [1,2,8,128] r8428 c8428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5295
  · exact u5296
  · exact u5297
  · exact u5298

def r8429 : Route 9 := (fun mask => (mask,id))

def c8429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u8429 : Upper (D 1) (R 1) [304,20,66,129] 13 := by
  apply FastRouting.sound _ _ [304,20,66,129] 13 (by decide) (choices 1) [2,8,32,64,128] r8429 c8429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5299
  · exact u5300
  · exact u5301
  · exact u5302
  · exact u5303

def b8430 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 369, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 70 138 249 233 233 233 489), lower := (rows 305 22 70 138 16 32 64 128 256), losses := [] }

theorem u8430 : Upper (D 1) (R 1) [304,20,66,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8430
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8431 : Route 9 := (fun mask => (mask,id))

def c8431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8431 : Upper (D 1) (R 1) [304,20,66,160] 13 := by
  apply FastRouting.sound _ _ [304,20,66,160] 13 (by decide) (choices 1) [1,2,8,64,128] r8431 c8431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5304
  · exact u5305
  · exact u5306
  · exact u5307
  · exact u5308

def r8432 : Route 9 := (fun mask => (mask,id))

def c8432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8432 : Upper (D 1) (R 1) [304,20,66,192] 13 := by
  apply FastRouting.sound _ _ [304,20,66,192] 13 (by decide) (choices 1) [1,2,8,32,128] r8432 c8432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5309
  · exact u5310
  · exact u5311
  · exact u5312
  · exact u5313

def b8433 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 305 22 76 11 242 226 226 226 482), lower := (rows 305 22 76 11 16 32 64 128 256), losses := [] }

theorem u8433 : Upper (D 1) (R 1) [304,20,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8433
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8434 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 22 76 41 210 226 194 194 450), lower := (rows 305 22 76 41 16 32 64 128 256), losses := [] }

theorem u8434 : Upper (D 1) (R 1) [304,20,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8434
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8435 : Route 9 := (fun mask => (mask,id))

def c8435 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8435 : Upper (D 1) (R 1) [304,20,72,34] 13 := by
  apply FastRouting.sound _ _ [304,20,72,34] 13 (by decide) (choices 1) [1,2,64,128] r8435 c8435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5314
  · exact u5315
  · exact u5316
  · exact u5317

def b8436 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 22 76 73 178 162 226 162 418), lower := (rows 305 22 76 73 16 32 64 128 256), losses := [] }

theorem u8436 : Upper (D 1) (R 1) [304,20,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8436
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8437 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 22 76 74 179 163 227 163 419), lower := (rows 305 22 76 74 16 32 64 128 256), losses := [] }

theorem u8437 : Upper (D 1) (R 1) [304,20,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8437
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8438 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 22 76 104 147 163 195 131 387), lower := (rows 305 22 76 104 16 32 64 128 256), losses := [] }

theorem u8438 : Upper (D 1) (R 1) [304,20,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8438
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8439 : Route 9 := (fun mask => (mask,id))

def c8439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8439 : Upper (D 1) (R 1) [304,20,72,129] 13 := by
  apply FastRouting.sound _ _ [304,20,72,129] 13 (by decide) (choices 1) [2,32,64,128] r8439 c8439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5318
  · exact u5319
  · exact u5320
  · exact u5321

def r8440 : Route 9 := (fun mask => (mask,id))

def c8440 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8440 : Upper (D 1) (R 1) [304,20,72,130] 13 := by
  apply FastRouting.sound _ _ [304,20,72,130] 13 (by decide) (choices 1) [1,2,32,64,128] r8440 c8440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5322
  · exact u5323
  · exact u5324
  · exact u5325
  · exact u5326

def r8441 : Route 9 := (fun mask => (mask,id))

def c8441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8441 : Upper (D 1) (R 1) [304,20,72,160] 13 := by
  apply FastRouting.sound _ _ [304,20,72,160] 13 (by decide) (choices 1) [1,2,64,128] r8441 c8441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5327
  · exact u5328
  · exact u5329
  · exact u5330

def b8442 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 22 76 200 179 163 227 163 419), lower := (rows 305 22 76 200 16 32 64 128 256), losses := [] }

theorem u8442 : Upper (D 1) (R 1) [304,20,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8442
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8443 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 305 22 100 11 218 234 202 202 458), lower := (rows 305 22 100 11 16 32 64 128 256), losses := [] }

theorem u8443 : Upper (D 1) (R 1) [304,20,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8443
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8444 : Route 9 := (fun mask => (mask,id))

def c8444 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8444 : Upper (D 1) (R 1) [304,20,96,65] 13 := by
  apply FastRouting.sound _ _ [304,20,96,65] 13 (by decide) (choices 1) [2,8,128] r8444 c8444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5331
  · exact u5332
  · exact u5333

def b8445 : PairBound 9 := { available := 139, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 74 155 171 203 139 395), lower := (rows 305 22 100 74 16 32 64 128 256), losses := [] }

theorem u8445 : Upper (D 1) (R 1) [304,20,96,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8446 : Route 9 := (fun mask => (mask,id))

def c8446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8446 : Upper (D 1) (R 1) [304,20,96,129] 13 := by
  apply FastRouting.sound _ _ [304,20,96,129] 13 (by decide) (choices 1) [2,8,64,128] r8446 c8446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5334
  · exact u5335
  · exact u5336
  · exact u5337

def r8447 : Route 9 := (fun mask => (mask,id))

def c8447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8447 : Upper (D 1) (R 1) [304,20,96,130] 13 := by
  apply FastRouting.sound _ _ [304,20,96,130] 13 (by decide) (choices 1) [1,2,8,64,128] r8447 c8447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5338
  · exact u5339
  · exact u5340
  · exact u5341
  · exact u5342

def r8448 : Route 9 := (fun mask => (mask,id))

def c8448 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8448 : Upper (D 1) (R 1) [304,20,96,192] 13 := by
  apply FastRouting.sound _ _ [304,20,96,192] 13 (by decide) (choices 1) [1,2,8,128] r8448 c8448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5343
  · exact u5344
  · exact u5345
  · exact u5346

def b8449 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 305 22 196 11 250 234 234 234 490), lower := (rows 305 22 196 11 16 32 64 128 256), losses := [] }

theorem u8449 : Upper (D 1) (R 1) [304,20,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8449
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8450 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 22 196 41 218 234 202 202 458), lower := (rows 305 22 196 41 16 32 64 128 256), losses := [] }

theorem u8450 : Upper (D 1) (R 1) [304,20,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8450
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8451 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8451 : Upper (D 1) (R 1) [304,20,192,34] 13 := by
  apply FastRouting.sound _ _ [304,20,192,34] 13 (by decide) (choices 1) [1,2,8,64] r8451 c8451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5347
  · exact u5348
  · exact u5349
  · exact u5350

def r8452 : Route 9 := (fun mask => (mask,id))

def c8452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8452 : Upper (D 1) (R 1) [304,20,192,65] 13 := by
  apply FastRouting.sound _ _ [304,20,192,65] 13 (by decide) (choices 1) [2,8,32,128] r8452 c8452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5351
  · exact u5352
  · exact u5353
  · exact u5354

def b8453 : PairBound 9 := { available := 171, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 196 74 187 171 235 171 427), lower := (rows 305 22 196 74 16 32 64 128 256), losses := [] }

theorem u8453 : Upper (D 1) (R 1) [304,20,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8453
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8454 : Route 9 := (fun mask => (mask,id))

def c8454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8454 : Upper (D 1) (R 1) [304,20,192,96] 13 := by
  apply FastRouting.sound _ _ [304,20,192,96] 13 (by decide) (choices 1) [1,2,8,128] r8454 c8454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5355
  · exact u5356
  · exact u5357
  · exact u5358

def b8455 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 22 196 200 59 43 107 171 299), lower := (rows 305 22 196 200 16 32 64 128 256), losses := [] }

theorem u8455 : Upper (D 1) (R 1) [304,20,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8455
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8456 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 14 14 240 240 240 240 496), lower := (rows 305 67 14 14 16 32 64 128 256), losses := [] }

theorem u8456 : Upper (D 1) (R 1) [304,65,10,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8456
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8457 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 14 26 244 228 228 228 484), lower := (rows 305 67 14 26 16 32 64 128 256), losses := [] }

theorem u8457 : Upper (D 1) (R 1) [304,65,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8457
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8458 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 305 67 14 28 242 226 226 226 482), lower := (rows 305 67 14 28 16 32 64 128 256), losses := [] }

theorem u8458 : Upper (D 1) (R 1) [304,65,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8458
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8459 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 67 14 56 214 230 198 198 454), lower := (rows 305 67 14 56 16 32 64 128 256), losses := [] }

theorem u8459 : Upper (D 1) (R 1) [304,65,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8459
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8459
end Delivery.IrregularNine14.P01
