import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0017

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2280 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 305 82 164 200 18 45 77 141 269), lower := (rows 305 82 164 200 18 32 64 128 256), losses := [] }

theorem u2280 : Upper (D 0) (R 0) [304,80,160,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2280
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2281 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 305 82 164 200 20 43 75 139 267), lower := (rows 305 82 164 200 20 32 64 128 256), losses := [] }

theorem u2281 : Upper (D 0) (R 0) [304,80,160,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2281
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2282 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 305 82 164 200 24 39 71 135 263), lower := (rows 305 82 164 200 24 32 64 128 256), losses := [] }

theorem u2282 : Upper (D 0) (R 0) [304,80,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2282
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2283 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 19 21 104 496 480 480 480 480), lower := (rows 15 19 21 104 16 32 64 128 256), losses := [] }

theorem u2283 : Upper (D 0) (R 0) [14,17,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2283
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2284 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 19 21 296 240 224 224 224 480), lower := (rows 15 19 21 296 16 32 64 128 256), losses := [] }

theorem u2284 : Upper (D 0) (R 0) [14,17,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2284
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2285 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 15 19 37 88 496 480 480 480 480), lower := (rows 15 19 37 88 16 32 64 128 256), losses := [] }

theorem u2285 : Upper (D 0) (R 0) [14,17,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2285
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2286 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 15 19 37 200 496 496 496 496 496), lower := (rows 15 19 37 200 16 32 64 128 256), losses := [] }

theorem u2286 : Upper (D 0) (R 0) [14,17,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2286
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2287 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 15 19 37 280 240 224 224 224 480), lower := (rows 15 19 37 280 16 32 64 128 256), losses := [] }

theorem u2287 : Upper (D 0) (R 0) [14,17,33,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2287
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2288 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 15 19 37 328 240 240 240 240 496), lower := (rows 15 19 37 328 16 32 64 128 256), losses := [] }

theorem u2288 : Upper (D 0) (R 0) [14,17,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2288
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2289 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 104 465 481 449 449 449), lower := (rows 15 19 52 104 16 32 64 128 256), losses := [] }

theorem u2289 : Upper (D 0) (R 0) [14,17,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2289
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2290 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 200 497 481 481 481 481), lower := (rows 15 19 52 200 16 32 64 128 256), losses := [] }

theorem u2290 : Upper (D 0) (R 0) [14,17,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2290
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2291 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 15 19 52 265 240 224 224 224 480), lower := (rows 15 19 52 265 16 32 64 128 256), losses := [] }

theorem u2291 : Upper (D 0) (R 0) [14,17,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2291
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2292 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 296 209 225 193 193 449), lower := (rows 15 19 52 296 16 32 64 128 256), losses := [] }

theorem u2292 : Upper (D 0) (R 0) [14,17,48,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2292
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2293 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 328 241 225 225 225 481), lower := (rows 15 19 52 328 16 32 64 128 256), losses := [] }

theorem u2293 : Upper (D 0) (R 0) [14,17,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2293
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2294 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 15 19 100 104 401 433 465 401 401), lower := (rows 15 19 100 104 16 32 64 128 256), losses := [] }

theorem u2294 : Upper (D 0) (R 0) [14,17,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2294
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2295 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 15 19 100 168 465 497 465 465 465), lower := (rows 15 19 100 168 16 32 64 128 256), losses := [] }

theorem u2295 : Upper (D 0) (R 0) [14,17,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2295
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2296 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 15 19 100 265 240 240 240 240 496), lower := (rows 15 19 100 265 16 32 64 128 256), losses := [] }

theorem u2296 : Upper (D 0) (R 0) [14,17,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2296
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2297 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 15 19 100 280 241 225 225 225 481), lower := (rows 15 19 100 280 16 32 64 128 256), losses := [] }

theorem u2297 : Upper (D 0) (R 0) [14,17,96,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2297
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2298 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 15 19 100 296 209 241 209 209 465), lower := (rows 15 19 100 296 16 32 64 128 256), losses := [] }

theorem u2298 : Upper (D 0) (R 0) [14,17,96,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2298
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2299 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2299 : Upper (D 0) (R 0) [14,17,96,384] 13 := by
  apply FastRouting.sound _ _ [14,17,96,384] 13 (by decide) (choices 1) [1,32,128] r2299 c2299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1023
  · exact u1024
  · exact u1025

def b2300 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 15 50 52 200 465 481 449 449 449), lower := (rows 15 50 52 200 16 32 64 128 256), losses := [] }

theorem u2300 : Upper (D 0) (R 0) [14,48,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2300
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2301 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 15 50 52 265 209 225 193 193 449), lower := (rows 15 50 52 265 16 32 64 128 256), losses := [] }

theorem u2301 : Upper (D 0) (R 0) [14,48,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2301
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2302 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 15 50 52 328 209 225 193 193 449), lower := (rows 15 50 52 328 16 32 64 128 256), losses := [] }

theorem u2302 : Upper (D 0) (R 0) [14,48,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2302
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2303 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 168 465 481 449 449 449), lower := (rows 15 50 84 168 16 32 64 128 256), losses := [] }

theorem u2303 : Upper (D 0) (R 0) [14,48,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2303
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2304 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 265 241 225 225 225 481), lower := (rows 15 50 84 265 16 32 64 128 256), losses := [] }

theorem u2304 : Upper (D 0) (R 0) [14,48,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2304
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2305 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 296 209 225 193 193 449), lower := (rows 15 50 84 296 16 32 64 128 256), losses := [] }

theorem u2305 : Upper (D 0) (R 0) [14,48,80,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2305
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2306 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 392 241 225 225 225 481), lower := (rows 15 50 84 392 16 32 64 128 256), losses := [] }

theorem u2306 : Upper (D 0) (R 0) [14,48,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2306
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2307 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2307 : Upper (D 0) (R 0) [14,48,192,257] 13 := by
  apply FastRouting.sound _ _ [14,48,192,257] 13 (by decide) (choices 1) [1,32,64] r2307 c2307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1026
  · exact u1027
  · exact u1028

def b2308 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 15 50 196 280 241 225 225 225 481), lower := (rows 15 50 196 280 16 32 64 128 256), losses := [] }

theorem u2308 : Upper (D 0) (R 0) [14,48,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2308
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2309 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 23 11 100 25 496 480 480 480 480), lower := (rows 23 11 100 25 16 32 64 128 256), losses := [] }

theorem u2309 : Upper (D 0) (R 0) [22,9,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2309
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2310 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 11 100 41 464 496 464 464 464), lower := (rows 23 11 100 41 16 32 64 128 256), losses := [] }

theorem u2310 : Upper (D 0) (R 0) [22,9,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2310
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2311 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 100 56 465 481 449 449 449), lower := (rows 23 11 100 56 16 32 64 128 256), losses := [] }

theorem u2311 : Upper (D 0) (R 0) [22,9,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2311
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2312 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 23 11 100 104 401 433 465 401 401), lower := (rows 23 11 100 104 16 32 64 128 256), losses := [] }

theorem u2312 : Upper (D 0) (R 0) [22,9,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2312
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2313 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 11 100 137 496 496 496 496 496), lower := (rows 23 11 100 137 16 32 64 128 256), losses := [] }

theorem u2313 : Upper (D 0) (R 0) [22,9,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2313
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2314 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 100 152 497 481 481 481 481), lower := (rows 23 11 100 152 16 32 64 128 256), losses := [] }

theorem u2314 : Upper (D 0) (R 0) [22,9,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2314
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2315 : Route 9 := (fun mask => (mask,id))

def c2315 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u2315 : Upper (D 0) (R 0) [22,9,96,160] 13 := by
  apply FastRouting.sound _ _ [22,9,96,160] 13 (by decide) (choices 1) [1,64,128,256] r2315 c2315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1029
  · exact u1030
  · exact u1031
  · exact u1032

def b2316 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 11 100 265 240 240 240 240 496), lower := (rows 23 11 100 265 16 32 64 128 256), losses := [] }

theorem u2316 : Upper (D 0) (R 0) [22,9,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2316
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2317 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 100 280 241 225 225 225 481), lower := (rows 23 11 100 280 16 32 64 128 256), losses := [] }

theorem u2317 : Upper (D 0) (R 0) [22,9,96,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2317
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2318 : Route 9 := (fun mask => (mask,id))

def c2318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2318 : Upper (D 0) (R 0) [22,9,96,288] 13 := by
  apply FastRouting.sound _ _ [22,9,96,288] 13 (by decide) (choices 1) [1,64,128] r2318 c2318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1033
  · exact u1034
  · exact u1035

def r2319 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2319 : Upper (D 0) (R 0) [22,9,96,384] 13 := by
  apply FastRouting.sound _ _ [22,9,96,384] 13 (by decide) (choices 1) [1,32,128] r2319 c2319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1036
  · exact u1037
  · exact u1038

def b2320 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 23 11 292 25 240 224 224 224 480), lower := (rows 23 11 292 25 16 32 64 128 256), losses := [] }

theorem u2320 : Upper (D 0) (R 0) [22,9,288,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2320
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2321 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 11 292 41 208 240 208 208 464), lower := (rows 23 11 292 41 16 32 64 128 256), losses := [] }

theorem u2321 : Upper (D 0) (R 0) [22,9,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2321
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2322 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 292 56 209 225 193 193 449), lower := (rows 23 11 292 56 16 32 64 128 256), losses := [] }

theorem u2322 : Upper (D 0) (R 0) [22,9,288,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2322
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2323 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 11 292 73 240 240 240 240 496), lower := (rows 23 11 292 73 16 32 64 128 256), losses := [] }

theorem u2323 : Upper (D 0) (R 0) [22,9,288,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2323
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2324 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 292 88 241 225 225 225 481), lower := (rows 23 11 292 88 16 32 64 128 256), losses := [] }

theorem u2324 : Upper (D 0) (R 0) [22,9,288,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2324
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2325 : Route 9 := (fun mask => (mask,id))

def c2325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2325 : Upper (D 0) (R 0) [22,9,288,96] 13 := by
  apply FastRouting.sound _ _ [22,9,288,96] 13 (by decide) (choices 1) [1,64,128] r2325 c2325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1039
  · exact u1040
  · exact u1041

def r2326 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2326 : Upper (D 0) (R 0) [22,9,288,192] 13 := by
  apply FastRouting.sound _ _ [22,9,288,192] 13 (by decide) (choices 1) [1,32,64] r2326 c2326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1042
  · exact u1043
  · exact u1044

def b2327 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 76 25 496 480 480 480 480), lower := (rows 23 35 76 25 16 32 64 128 256), losses := [] }

theorem u2327 : Upper (D 0) (R 0) [22,33,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2327
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2328 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 35 76 41 464 496 464 464 464), lower := (rows 23 35 76 41 16 32 64 128 256), losses := [] }

theorem u2328 : Upper (D 0) (R 0) [22,33,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2328
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2329 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 76 56 465 481 449 449 449), lower := (rows 23 35 76 56 16 32 64 128 256), losses := [] }

theorem u2329 : Upper (D 0) (R 0) [22,33,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2329
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2330 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 35 76 73 432 432 496 432 432), lower := (rows 23 35 76 73 16 32 64 128 256), losses := [] }

theorem u2330 : Upper (D 0) (R 0) [22,33,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2330
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2331 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 76 88 433 417 481 417 417), lower := (rows 23 35 76 88 16 32 64 128 256), losses := [] }

theorem u2331 : Upper (D 0) (R 0) [22,33,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2331
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2332 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 76 104 401 433 465 401 401), lower := (rows 23 35 76 104 16 32 64 128 256), losses := [] }

theorem u2332 : Upper (D 0) (R 0) [22,33,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2332
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2333 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 76 137 496 496 496 496 496), lower := (rows 23 35 76 137 16 32 64 128 256), losses := [] }

theorem u2333 : Upper (D 0) (R 0) [22,33,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2333
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2334 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 76 152 497 481 481 481 481), lower := (rows 23 35 76 152 16 32 64 128 256), losses := [] }

theorem u2334 : Upper (D 0) (R 0) [22,33,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2334
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2335 : Route 9 := (fun mask => (mask,id))

def c2335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u2335 : Upper (D 0) (R 0) [22,33,72,160] 13 := by
  apply FastRouting.sound _ _ [22,33,72,160] 13 (by decide) (choices 1) [1,64,128,256] r2335 c2335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1045
  · exact u1046
  · exact u1047
  · exact u1048

def b2336 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 76 200 433 433 497 433 433), lower := (rows 23 35 76 200 16 32 64 128 256), losses := [] }

theorem u2336 : Upper (D 0) (R 0) [22,33,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2336
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2337 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 76 265 240 240 240 240 496), lower := (rows 23 35 76 265 16 32 64 128 256), losses := [] }

theorem u2337 : Upper (D 0) (R 0) [22,33,72,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2337
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2338 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 76 280 241 225 225 225 481), lower := (rows 23 35 76 280 16 32 64 128 256), losses := [] }

theorem u2338 : Upper (D 0) (R 0) [22,33,72,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2338
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2339 : Route 9 := (fun mask => (mask,id))

def c2339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2339 : Upper (D 0) (R 0) [22,33,72,288] 13 := by
  apply FastRouting.sound _ _ [22,33,72,288] 13 (by decide) (choices 1) [1,64,128] r2339 c2339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1049
  · exact u1050
  · exact u1051

#print axioms u2339
end Delivery.IrregularNine14.P00
