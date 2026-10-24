import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0007

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2280 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 11 276 104 49 225 193 193 449), lower := (rows 7 11 276 104 49 32 64 128 256), losses := [] }

theorem u2280 : Upper (D 3) (R 3) [6,9,272,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2280
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2281 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 276 104 112 161 193 129 385), lower := (rows 7 11 276 104 112 32 64 128 256), losses := [] }

theorem u2281 : Upper (D 3) (R 3) [6,9,272,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2281
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2282 : Route 9 := (fun mask => (mask,id))

def c2282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2282 : Upper (D 3) (R 3) [6,9,272,96,129] 13 := by
  apply FastRouting.sound _ _ [6,9,272,96,129] 13 (by decide) (choices 1) [1,64,128] r2282 c2282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u442
  · exact u443
  · exact u444

def r2283 : Route 9 := (fun mask => (mask,id))

def c2283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2283 : Upper (D 3) (R 3) [6,9,272,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,272,96,160] 13 (by decide) (choices 1) [1,64,128] r2283 c2283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u445
  · exact u446
  · exact u447

def b2284 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 88 49 225 193 193 449), lower := (rows 7 11 292 88 49 32 64 128 256), losses := [] }

theorem u2284 : Upper (D 3) (R 3) [6,9,288,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2284
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2285 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 88 81 161 225 161 417), lower := (rows 7 11 292 88 81 32 64 128 256), losses := [] }

theorem u2285 : Upper (D 3) (R 3) [6,9,288,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2285
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2286 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 292 88 112 161 193 129 385), lower := (rows 7 11 292 88 112 32 64 128 256), losses := [] }

theorem u2286 : Upper (D 3) (R 3) [6,9,288,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2286
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2287 : Route 9 := (fun mask => (mask,id))

def c2287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2287 : Upper (D 3) (R 3) [6,9,288,80,129] 13 := by
  apply FastRouting.sound _ _ [6,9,288,80,129] 13 (by decide) (choices 1) [1,64,128] r2287 c2287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u448
  · exact u449
  · exact u450

def r2288 : Route 9 := (fun mask => (mask,id))

def c2288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2288 : Upper (D 3) (R 3) [6,9,288,80,160] 13 := by
  apply FastRouting.sound _ _ [6,9,288,80,160] 13 (by decide) (choices 1) [1,64,128] r2288 c2288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u451
  · exact u452
  · exact u453

def b2289 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 292 88 208 161 225 161 417), lower := (rows 7 11 292 88 208 32 64 128 256), losses := [] }

theorem u2289 : Upper (D 3) (R 3) [6,9,288,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2289
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2290 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 292 200 49 241 209 209 465), lower := (rows 7 11 292 200 49 32 64 128 256), losses := [] }

theorem u2290 : Upper (D 3) (R 3) [6,9,288,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2290
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2291 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 11 292 200 81 177 241 177 433), lower := (rows 7 11 292 200 81 32 64 128 256), losses := [] }

theorem u2291 : Upper (D 3) (R 3) [6,9,288,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2291
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2292 : Route 9 := (fun mask => (mask,id))

def c2292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2292 : Upper (D 3) (R 3) [6,9,288,192,96] 13 := by
  apply FastRouting.sound _ _ [6,9,288,192,96] 13 (by decide) (choices 1) [1,16,128] r2292 c2292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u454
  · exact u455
  · exact u456

def b2293 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 292 200 208 49 113 177 305), lower := (rows 7 11 292 200 208 32 64 128 256), losses := [] }

theorem u2293 : Upper (D 3) (R 3) [6,9,288,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2293
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2294 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 37 41 81 480 448 448 448), lower := (rows 7 26 37 41 81 32 64 128 256), losses := [] }

theorem u2294 : Upper (D 3) (R 3) [6,24,33,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2294
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2295 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 37 41 208 481 449 449 449), lower := (rows 7 26 37 41 208 32 64 128 256), losses := [] }

theorem u2295 : Upper (D 3) (R 3) [6,24,33,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2295
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2296 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 37 41 273 224 192 192 448), lower := (rows 7 26 37 41 273 32 64 128 256), losses := [] }

theorem u2296 : Upper (D 3) (R 3) [6,24,33,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2296
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2297 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 37 41 336 225 193 193 449), lower := (rows 7 26 37 41 336 32 64 128 256), losses := [] }

theorem u2297 : Upper (D 3) (R 3) [6,24,33,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2297
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2298 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 37 73 81 416 480 416 416), lower := (rows 7 26 37 73 81 32 64 128 256), losses := [] }

theorem u2298 : Upper (D 3) (R 3) [6,24,33,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2298
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2299 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 37 73 112 417 449 385 385), lower := (rows 7 26 37 73 112 32 64 128 256), losses := [] }

theorem u2299 : Upper (D 3) (R 3) [6,24,33,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2299
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m2300_128 : Upper (D 3) (R 3) [6,24,33,65,129,128] 13 :=
  permutation_upper _ _ _ [6,24,33,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u457

def r2300 : Route 9 := (fun mask => (mask,id))

def c2300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u2300 : Upper (D 3) (R 3) [6,24,33,65,129] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,129] 13 (by decide) (choices 1) [64,128,256] r2300 c2300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u457
  · exact m2300_128
  · exact u458

def b2301 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 37 73 176 481 449 449 449), lower := (rows 7 26 37 73 176 32 64 128 256), losses := [] }

theorem u2301 : Upper (D 3) (R 3) [6,24,33,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2301
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2302 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 73 208 417 481 417 417), lower := (rows 7 26 37 73 208 32 64 128 256), losses := [] }

theorem u2302 : Upper (D 3) (R 3) [6,24,33,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2302
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2303 : Route 9 := (fun mask => (mask,id))

def c2303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2303 : Upper (D 3) (R 3) [6,24,33,65,257] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,257] 13 (by decide) (choices 1) [64,128] r2303 c2303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u459
  · exact u460

def b2304 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 37 73 304 225 193 193 449), lower := (rows 7 26 37 73 304 32 64 128 256), losses := [] }

theorem u2304 : Upper (D 3) (R 3) [6,24,33,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2304
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2305 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 73 336 161 225 161 417), lower := (rows 7 26 37 73 336 32 64 128 256), losses := [] }

theorem u2305 : Upper (D 3) (R 3) [6,24,33,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2305
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2306 : Route 9 := (fun mask => (mask,id))

def c2306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2306 : Upper (D 3) (R 3) [6,24,33,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,384] 13 (by decide) (choices 1) [1,64,128] r2306 c2306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u461
  · exact u462
  · exact u463

def b2307 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 208 417 449 385 385), lower := (rows 7 26 37 104 208 32 64 128 256), losses := [] }

theorem u2307 : Upper (D 3) (R 3) [6,24,33,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2307
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2308 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 26 37 104 273 225 193 193 449), lower := (rows 7 26 37 104 273 32 64 128 256), losses := [] }

theorem u2308 : Upper (D 3) (R 3) [6,24,33,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2308
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2309 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 104 336 161 193 129 385), lower := (rows 7 26 37 104 336 32 64 128 256), losses := [] }

theorem u2309 : Upper (D 3) (R 3) [6,24,33,96,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2309
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2310 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 26 37 104 400 225 193 193 449), lower := (rows 7 26 37 104 400 32 64 128 256), losses := [] }

theorem u2310 : Upper (D 3) (R 3) [6,24,33,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2310
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2311 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 200 208 289 353 417 289), lower := (rows 7 26 37 200 208 32 64 128 256), losses := [] }

theorem u2311 : Upper (D 3) (R 3) [6,24,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2311
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2312 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2312 : Upper (D 3) (R 3) [6,24,33,192,257] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,257] 13 (by decide) (choices 1) [1,64] r2312 c2312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u464
  · exact u465

def b2313 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 37 200 304 225 193 193 449), lower := (rows 7 26 37 200 304 32 64 128 256), losses := [] }

theorem u2313 : Upper (D 3) (R 3) [6,24,33,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2313
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2314 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 200 336 161 225 161 417), lower := (rows 7 26 37 200 336 32 64 128 256), losses := [] }

theorem u2314 : Upper (D 3) (R 3) [6,24,33,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2314
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2315 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 100 41 145 481 449 449 449), lower := (rows 7 26 100 41 145 32 64 128 256), losses := [] }

theorem u2315 : Upper (D 3) (R 3) [6,24,96,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2315
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2316 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 100 41 273 225 193 193 449), lower := (rows 7 26 100 41 273 32 64 128 256), losses := [] }

theorem u2316 : Upper (D 3) (R 3) [6,24,96,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2316
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2317 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 100 41 400 225 193 193 449), lower := (rows 7 26 100 41 400 32 64 128 256), losses := [] }

theorem u2317 : Upper (D 3) (R 3) [6,24,96,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2317
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2318 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 145 417 449 385 385), lower := (rows 7 26 100 104 145 32 64 128 256), losses := [] }

theorem u2318 : Upper (D 3) (R 3) [6,24,96,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2318
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2319 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 273 161 193 129 385), lower := (rows 7 26 100 104 273 32 64 128 256), losses := [] }

theorem u2319 : Upper (D 3) (R 3) [6,24,96,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2319
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2320 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 100 104 400 161 193 129 385), lower := (rows 7 26 100 104 400 32 64 128 256), losses := [] }

theorem u2320 : Upper (D 3) (R 3) [6,24,96,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2320
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2321 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 100 137 145 353 353 481 353), lower := (rows 7 26 100 137 145 32 64 128 256), losses := [] }

theorem u2321 : Upper (D 3) (R 3) [6,24,96,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2321
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2322 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 137 176 353 321 449 321), lower := (rows 7 26 100 137 176 32 64 128 256), losses := [] }

theorem u2322 : Upper (D 3) (R 3) [6,24,96,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2322
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2323 : Route 9 := (fun mask => (mask,id))

def c2323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2323 : Upper (D 3) (R 3) [6,24,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257] 13 (by decide) (choices 1) [1,64,128] r2323 c2323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u466
  · exact u467
  · exact u468

def b2324 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 100 137 304 225 193 193 449), lower := (rows 7 26 100 137 304 32 64 128 256), losses := [] }

theorem u2324 : Upper (D 3) (R 3) [6,24,96,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2324
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2325 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 137 400 97 97 225 353), lower := (rows 7 26 100 137 400 32 64 128 256), losses := [] }

theorem u2325 : Upper (D 3) (R 3) [6,24,96,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2325
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2326 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 7 26 100 168 273 225 193 193 449), lower := (rows 7 26 100 168 273 32 64 128 256), losses := [] }

theorem u2326 : Upper (D 3) (R 3) [6,24,96,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2326
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2327 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 168 400 97 65 193 321), lower := (rows 7 26 100 168 400 32 64 128 256), losses := [] }

theorem u2327 : Upper (D 3) (R 3) [6,24,96,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2327
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2328 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 261 41 49 224 192 192 448), lower := (rows 7 26 261 41 49 32 64 128 256), losses := [] }

theorem u2328 : Upper (D 3) (R 3) [6,24,257,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2328
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2329 : Route 9 := (fun mask => (mask,id))

def c2329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2329 : Upper (D 3) (R 3) [6,24,257,33,65] 13 := by
  apply FastRouting.sound _ _ [6,24,257,33,65] 13 (by decide) (choices 1) [64,128] r2329 c2329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u469
  · exact u470

def b2330 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 26 261 41 112 225 193 193 449), lower := (rows 7 26 261 41 112 32 64 128 256), losses := [] }

theorem u2330 : Upper (D 3) (R 3) [6,24,257,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2330
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2331 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2331 : Upper (D 3) (R 3) [6,24,257,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,257,33,192] 13 (by decide) (choices 1) [1,64] r2331 c2331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u471
  · exact u472

def b2332 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 261 104 112 161 193 129 385), lower := (rows 7 26 261 104 112 32 64 128 256), losses := [] }

theorem u2332 : Upper (D 3) (R 3) [6,24,257,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2332
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2333 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 26 261 104 176 225 193 193 449), lower := (rows 7 26 261 104 176 32 64 128 256), losses := [] }

theorem u2333 : Upper (D 3) (R 3) [6,24,257,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2333
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2334 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 292 41 81 225 193 193 449), lower := (rows 7 26 292 41 81 32 64 128 256), losses := [] }

theorem u2334 : Upper (D 3) (R 3) [6,24,288,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2334
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2335 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 292 41 208 225 193 193 449), lower := (rows 7 26 292 41 208 32 64 128 256), losses := [] }

theorem u2335 : Upper (D 3) (R 3) [6,24,288,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2335
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2336 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 7 26 292 73 81 161 225 161 417), lower := (rows 7 26 292 73 81 32 64 128 256), losses := [] }

theorem u2336 : Upper (D 3) (R 3) [6,24,288,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2336
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2337 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 292 73 112 161 193 129 385), lower := (rows 7 26 292 73 112 32 64 128 256), losses := [] }

theorem u2337 : Upper (D 3) (R 3) [6,24,288,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2337
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m2338_128 : Upper (D 3) (R 3) [6,24,288,65,129,128] 13 :=
  permutation_upper _ _ _ [6,24,288,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u474

def r2338 : Route 9 := (fun mask => (mask,id))

def c2338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2338 : Upper (D 3) (R 3) [6,24,288,65,129] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,129] 13 (by decide) (choices 1) [1,64,128] r2338 c2338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u473
  · exact u474
  · exact m2338_128

def b2339 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 26 292 73 176 225 193 193 449), lower := (rows 7 26 292 73 176 32 64 128 256), losses := [] }

theorem u2339 : Upper (D 3) (R 3) [6,24,288,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2339
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2339
end Delivery.IrregularNine14.P03
