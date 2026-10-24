import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0000
import IrregularNine14P04C0001

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b300 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 200 28 305 337 401 273), lower := (rows 7 11 38 200 28 32 64 128 256), losses := [] }

theorem u300 : Upper (D 4) (R 4) [6,9,34,192,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b300
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 200 273 60 92 156 284), lower := (rows 7 11 38 200 273 32 64 128 256), losses := [] }

theorem u301 : Upper (D 4) (R 4) [6,9,34,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b301
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 200 276 57 89 153 281), lower := (rows 7 11 38 200 276 32 64 128 256), losses := [] }

theorem u302 : Upper (D 4) (R 4) [6,9,34,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b302
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 200 280 53 85 149 277), lower := (rows 7 11 38 200 280 32 64 128 256), losses := [] }

theorem u303 : Upper (D 4) (R 4) [6,9,34,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b303
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 11 44 76 145 306 338 402 274), lower := (rows 7 11 44 76 145 32 64 128 256), losses := [] }

theorem u304 : Upper (D 4) (R 4) [6,9,40,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b304
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 11 44 76 400 51 83 147 275), lower := (rows 7 11 44 76 400 32 64 128 256), losses := [] }

theorem u305 : Upper (D 4) (R 4) [6,9,40,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b305
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 278, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 88 145 310 342 406 278), lower := (rows 7 11 44 88 145 32 64 128 256), losses := [] }

theorem u306 : Upper (D 4) (R 4) [6,9,40,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b306
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 277, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 88 146 309 341 405 277), lower := (rows 7 11 44 88 146 32 64 128 256), losses := [] }

theorem u307 : Upper (D 4) (R 4) [6,9,40,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b307
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 88 148 307 339 403 275), lower := (rows 7 11 44 88 148 32 64 128 256), losses := [] }

theorem u308 : Upper (D 4) (R 4) [6,9,40,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b308
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 88 400 55 87 151 279), lower := (rows 7 11 44 88 400 32 64 128 256), losses := [] }

theorem u309 : Upper (D 4) (R 4) [6,9,40,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b309
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 200 273 54 86 150 278), lower := (rows 7 11 44 200 273 32 64 128 256), losses := [] }

theorem u310 : Upper (D 4) (R 4) [6,9,40,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b310
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 200 274 53 85 149 277), lower := (rows 7 11 44 200 274 32 64 128 256), losses := [] }

theorem u311 : Upper (D 4) (R 4) [6,9,40,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b311
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 200 276 51 83 147 275), lower := (rows 7 11 44 200 276 32 64 128 256), losses := [] }

theorem u312 : Upper (D 4) (R 4) [6,9,40,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b312
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 396, camps := [{ cop := 4, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 88 19 428 460 396 396), lower := (rows 7 11 52 88 19 32 64 128 256), losses := [] }

theorem u313 : Upper (D 4) (R 4) [6,9,48,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b313
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 16, targets := 2 }], pairs := [(4,1)], upper := (rows 7 11 52 88 21 426 458 394 394), lower := (rows 7 11 52 88 21 32 64 128 256), losses := [] }

theorem u314 : Upper (D 4) (R 4) [6,9,48,80,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b314
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 52 88 22 425 457 393 393), lower := (rows 7 11 52 88 22 32 64 128 256), losses := [] }

theorem u315 : Upper (D 4) (R 4) [6,9,48,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b315
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 52 88 28 419 451 387 387), lower := (rows 7 11 52 88 28 32 64 128 256), losses := [] }

theorem u316 : Upper (D 4) (R 4) [6,9,48,80,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b316
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r317 : Route 9 := (fun mask => (mask,id))

def c317 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u317 : Upper (D 4) (R 4) [6,9,48,80,129] 13 := by
  apply FastRouting.sound _ _ [6,9,48,80,129] 13 (by decide) (choices 1) [2,4,8,256] r317 c317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38
  · exact u39
  · exact u40
  · exact u41

def r318 : Route 9 := (fun mask => (mask,id))

def c318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u318 : Upper (D 4) (R 4) [6,9,48,80,132] 13 := by
  apply FastRouting.sound _ _ [6,9,48,80,132] 13 (by decide) (choices 1) [1,2,8,256] r318 c318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u42
  · exact u43
  · exact u44
  · exact u45

def r319 : Route 9 := (fun mask => (mask,id))

def c319 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u319 : Upper (D 4) (R 4) [6,9,48,80,384] 13 := by
  apply FastRouting.sound _ _ [6,9,48,80,384] 13 (by decide) (choices 1) [1,2,4,8] r319 c319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u46
  · exact u47
  · exact u48
  · exact u49

def b320 : PairBound 9 := { available := 284, camps := [{ cop := 4, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 200 19 316 348 412 284), lower := (rows 7 11 52 200 19 32 64 128 256), losses := [] }

theorem u320 : Upper (D 4) (R 4) [6,9,48,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b320
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b321 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 16, targets := 2 }], pairs := [(4,1)], upper := (rows 7 11 52 200 21 314 346 410 282), lower := (rows 7 11 52 200 21 32 64 128 256), losses := [] }

theorem u321 : Upper (D 4) (R 4) [6,9,48,192,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b321
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b322 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 52 200 22 313 345 409 281), lower := (rows 7 11 52 200 22 32 64 128 256), losses := [] }

theorem u322 : Upper (D 4) (R 4) [6,9,48,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b322
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 278, camps := [{ cop := 1, region := 16, targets := 2 }], pairs := [(4,1)], upper := (rows 7 11 52 200 25 310 342 406 278), lower := (rows 7 11 52 200 25 32 64 128 256), losses := [] }

theorem u323 : Upper (D 4) (R 4) [6,9,48,192,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b323
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 52 200 26 309 341 405 277), lower := (rows 7 11 52 200 26 32 64 128 256), losses := [] }

theorem u324 : Upper (D 4) (R 4) [6,9,48,192,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b324
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 275, camps := [{ cop := 4, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 52 200 28 307 339 403 275), lower := (rows 7 11 52 200 28 32 64 128 256), losses := [] }

theorem u325 : Upper (D 4) (R 4) [6,9,48,192,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b325
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r326 : Route 9 := (fun mask => (mask,id))

def c326 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u326 : Upper (D 4) (R 4) [6,9,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,257] 13 (by decide) (choices 1) [2,4,8,16] r326 c326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u50
  · exact u51
  · exact u52
  · exact u53

def r327 : Route 9 := (fun mask => (mask,id))

def c327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u327 : Upper (D 4) (R 4) [6,9,48,192,258] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,258] 13 (by decide) (choices 1) [1,4,8,16] r327 c327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u54
  · exact u55
  · exact u56
  · exact u57

def r328 : Route 9 := (fun mask => (mask,id))

def c328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u328 : Upper (D 4) (R 4) [6,9,48,192,260] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,260] 13 (by decide) (choices 1) [1,2,8,16] r328 c328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u58
  · exact u59
  · exact u60
  · exact u61

def r329 : Route 9 := (fun mask => (mask,id))

def c329 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u329 : Upper (D 4) (R 4) [6,9,48,192,264] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,264] 13 (by decide) (choices 1) [1,2,4,16] r329 c329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u62
  · exact u63
  · exact u64
  · exact u65

def b330 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 392 19 60 92 156 284), lower := (rows 7 11 100 392 19 32 64 128 256), losses := [] }

theorem u330 : Upper (D 4) (R 4) [6,9,96,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b330
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b331 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 16, targets := 2 }], pairs := [(4,1)], upper := (rows 7 11 100 392 21 58 90 154 282), lower := (rows 7 11 100 392 21 32 64 128 256), losses := [] }

theorem u331 : Upper (D 4) (R 4) [6,9,96,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b331
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 392 22 57 89 153 281), lower := (rows 7 11 100 392 22 32 64 128 256), losses := [] }

theorem u332 : Upper (D 4) (R 4) [6,9,96,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b332
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 100 392 28 51 83 147 275), lower := (rows 7 11 100 392 28 32 64 128 256), losses := [] }

theorem u333 : Upper (D 4) (R 4) [6,9,96,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b333
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 28 41 82 433 465 401 401), lower := (rows 7 14 28 41 82 32 64 128 256), losses := [] }

theorem u334 : Upper (D 4) (R 4) [6,12,24,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b334
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 28 41 208 307 339 403 275), lower := (rows 7 14 28 41 208 32 64 128 256), losses := [] }

theorem u335 : Upper (D 4) (R 4) [6,12,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b335
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 464, targets := 2 }], pairs := [(4,1)], upper := (rows 7 14 28 42 81 433 465 401 401), lower := (rows 7 14 28 42 81 32 64 128 256), losses := [] }

theorem u336 : Upper (D 4) (R 4) [6,12,24,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b336
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 28 104 145 307 339 403 275), lower := (rows 7 14 28 104 145 32 64 128 256), losses := [] }

theorem u337 : Upper (D 4) (R 4) [6,12,24,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b337
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 28 104 400 51 83 147 275), lower := (rows 7 14 28 104 400 32 64 128 256), losses := [] }

theorem u338 : Upper (D 4) (R 4) [6,12,24,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b338
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 25 88 434 466 402 402), lower := (rows 7 14 37 25 88 32 64 128 256), losses := [] }

theorem u339 : Upper (D 4) (R 4) [6,12,33,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b339
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 25 208 314 346 410 282), lower := (rows 7 14 37 25 208 32 64 128 256), losses := [] }

theorem u340 : Upper (D 4) (R 4) [6,12,33,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b340
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 73 152 306 338 402 274), lower := (rows 7 14 37 73 152 32 64 128 256), losses := [] }

theorem u341 : Upper (D 4) (R 4) [6,12,33,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b341
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 73 400 58 90 154 282), lower := (rows 7 14 37 73 400 32 64 128 256), losses := [] }

theorem u342 : Upper (D 4) (R 4) [6,12,33,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b342
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 74 152 305 337 401 273), lower := (rows 7 14 37 74 152 32 64 128 256), losses := [] }

theorem u343 : Upper (D 4) (R 4) [6,12,33,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b343
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 74 400 57 89 153 281), lower := (rows 7 14 37 74 400 32 64 128 256), losses := [] }

theorem u344 : Upper (D 4) (R 4) [6,12,33,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b344
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 88 25 434 466 402 402), lower := (rows 7 14 37 88 25 32 64 128 256), losses := [] }

theorem u345 : Upper (D 4) (R 4) [6,12,33,80,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b345
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 88 145 314 346 410 282), lower := (rows 7 14 37 88 145 32 64 128 256), losses := [] }

theorem u346 : Upper (D 4) (R 4) [6,12,33,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b346
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 88 146 313 345 409 281), lower := (rows 7 14 37 88 146 32 64 128 256), losses := [] }

theorem u347 : Upper (D 4) (R 4) [6,12,33,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b347
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 88 152 307 339 403 275), lower := (rows 7 14 37 88 152 32 64 128 256), losses := [] }

theorem u348 : Upper (D 4) (R 4) [6,12,33,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b348
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 88 400 59 91 155 283), lower := (rows 7 14 37 88 400 32 64 128 256), losses := [] }

theorem u349 : Upper (D 4) (R 4) [6,12,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b349
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 200 25 306 338 402 274), lower := (rows 7 14 37 200 25 32 64 128 256), losses := [] }

theorem u350 : Upper (D 4) (R 4) [6,12,33,192,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b350
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 200 273 58 90 154 282), lower := (rows 7 14 37 200 273 32 64 128 256), losses := [] }

theorem u351 : Upper (D 4) (R 4) [6,12,33,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b351
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 200 274 57 89 153 281), lower := (rows 7 14 37 200 274 32 64 128 256), losses := [] }

theorem u352 : Upper (D 4) (R 4) [6,12,33,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b352
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 200 280 51 83 147 275), lower := (rows 7 14 37 200 280 32 64 128 256), losses := [] }

theorem u353 : Upper (D 4) (R 4) [6,12,33,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b353
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 25 88 433 465 401 401), lower := (rows 7 14 38 25 88 32 64 128 256), losses := [] }

theorem u354 : Upper (D 4) (R 4) [6,12,34,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b354
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 25 208 313 345 409 281), lower := (rows 7 14 38 25 208 32 64 128 256), losses := [] }

theorem u355 : Upper (D 4) (R 4) [6,12,34,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b355
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 73 400 57 89 153 281), lower := (rows 7 14 38 73 400 32 64 128 256), losses := [] }

theorem u356 : Upper (D 4) (R 4) [6,12,34,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b356
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 88 25 433 465 401 401), lower := (rows 7 14 38 88 25 32 64 128 256), losses := [] }

theorem u357 : Upper (D 4) (R 4) [6,12,34,80,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b357
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 88 145 313 345 409 281), lower := (rows 7 14 38 88 145 32 64 128 256), losses := [] }

theorem u358 : Upper (D 4) (R 4) [6,12,34,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b358
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 88 152 305 337 401 273), lower := (rows 7 14 38 88 152 32 64 128 256), losses := [] }

theorem u359 : Upper (D 4) (R 4) [6,12,34,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b359
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P04
