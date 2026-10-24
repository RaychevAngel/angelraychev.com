import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0007

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2280 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 137 304 34 76 140 268), lower := (rows 7 35 84 137 304 34 64 128 256), losses := [] }

theorem u2280 : Upper (D 5) (R 5) [6,33,80,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2280
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2281 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 35 84 137 304 36 74 138 266), lower := (rows 7 35 84 137 304 36 64 128 256), losses := [] }

theorem u2281 : Upper (D 5) (R 5) [6,33,80,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2281
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2282 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 136, targets := 32 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(3,5)], upper := (rows 7 35 84 137 304 40 78 142 270), lower := (rows 7 35 84 137 304 40 64 128 256), losses := [] }

theorem u2282 : Upper (D 5) (R 5) [6,33,80,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2282
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2283 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 138 56 33 332 396 268), lower := (rows 7 35 84 138 56 33 64 128 256), losses := [] }

theorem u2283 : Upper (D 5) (R 5) [6,33,80,130,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2283
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2284 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 35 84 138 56 36 329 393 265), lower := (rows 7 35 84 138 56 36 64 128 256), losses := [] }

theorem u2284 : Upper (D 5) (R 5) [6,33,80,130,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2284
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2285 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 84 138 56 40 325 389 261), lower := (rows 7 35 84 138 56 40 64 128 256), losses := [] }

theorem u2285 : Upper (D 5) (R 5) [6,33,80,130,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2285
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2286 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 84 138 56 288 77 141 269), lower := (rows 7 35 84 138 56 288 64 128 256), losses := [] }

theorem u2286 : Upper (D 5) (R 5) [6,33,80,130,40,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2286
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2287 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 138 280 33 108 172 300), lower := (rows 7 35 84 138 280 33 64 128 256), losses := [] }

theorem u2287 : Upper (D 5) (R 5) [6,33,80,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2287
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2288 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 84 138 280 36 105 169 297), lower := (rows 7 35 84 138 280 36 64 128 256), losses := [] }

theorem u2288 : Upper (D 5) (R 5) [6,33,80,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2288
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2289 : Route 9 := (fun mask => (mask,id))

def c2289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2289 : Upper (D 5) (R 5) [6,33,80,130,264,8] 13 := by
  apply FastRouting.sound _ _ [6,33,80,130,264,8] 13 (by decide) (choices 1) [1,4,32] r2289 c2289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u420
  · exact u421
  · exact u422

def b2290 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 138 304 33 76 140 268), lower := (rows 7 35 84 138 304 33 64 128 256), losses := [] }

theorem u2290 : Upper (D 5) (R 5) [6,33,80,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2290
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2291 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 35 84 138 304 36 73 137 265), lower := (rows 7 35 84 138 304 36 64 128 256), losses := [] }

theorem u2291 : Upper (D 5) (R 5) [6,33,80,130,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2291
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2292 : Route 9 := (fun mask => (mask,id))

def c2292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2292 : Upper (D 5) (R 5) [6,33,80,130,288,8] 13 := by
  apply FastRouting.sound _ _ [6,33,80,130,288,8] 13 (by decide) (choices 1) [1,4,8] r2292 c2292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u423
  · exact u424
  · exact u425

def b2293 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 140 56 33 330 394 266), lower := (rows 7 35 84 140 56 33 64 128 256), losses := [] }

theorem u2293 : Upper (D 5) (R 5) [6,33,80,132,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2293
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2294 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 140 56 34 329 393 265), lower := (rows 7 35 84 140 56 34 64 128 256), losses := [] }

theorem u2294 : Upper (D 5) (R 5) [6,33,80,132,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2294
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2295 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 84 140 56 40 323 387 259), lower := (rows 7 35 84 140 56 40 64 128 256), losses := [] }

theorem u2295 : Upper (D 5) (R 5) [6,33,80,132,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2295
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2296 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 84 140 56 288 75 139 267), lower := (rows 7 35 84 140 56 288 64 128 256), losses := [] }

theorem u2296 : Upper (D 5) (R 5) [6,33,80,132,40,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2296
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2297 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 140 280 33 106 170 298), lower := (rows 7 35 84 140 280 33 64 128 256), losses := [] }

theorem u2297 : Upper (D 5) (R 5) [6,33,80,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2297
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2298 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 140 280 34 105 169 297), lower := (rows 7 35 84 140 280 34 64 128 256), losses := [] }

theorem u2298 : Upper (D 5) (R 5) [6,33,80,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2298
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2299 : Route 9 := (fun mask => (mask,id))

def c2299 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2299 : Upper (D 5) (R 5) [6,33,80,132,264,8] 13 := by
  apply FastRouting.sound _ _ [6,33,80,132,264,8] 13 (by decide) (choices 1) [1,2,32] r2299 c2299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u426
  · exact u427
  · exact u428

def b2300 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 140 304 33 74 138 266), lower := (rows 7 35 84 140 304 33 64 128 256), losses := [] }

theorem u2300 : Upper (D 5) (R 5) [6,33,80,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2300
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2301 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 140 304 34 73 137 265), lower := (rows 7 35 84 140 304 34 64 128 256), losses := [] }

theorem u2301 : Upper (D 5) (R 5) [6,33,80,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2301
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2302 : Route 9 := (fun mask => (mask,id))

def c2302 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2302 : Upper (D 5) (R 5) [6,33,80,132,288,8] 13 := by
  apply FastRouting.sound _ _ [6,33,80,132,288,8] 13 (by decide) (choices 1) [1,2,8] r2302 c2302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u429
  · exact u430
  · exact u431

def b2303 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 168 274 33 76 140 268), lower := (rows 7 35 84 168 274 33 64 128 256), losses := [] }

theorem u2303 : Upper (D 5) (R 5) [6,33,80,160,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2303
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2304 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 84 168 274 36 73 137 265), lower := (rows 7 35 84 168 274 36 64 128 256), losses := [] }

theorem u2304 : Upper (D 5) (R 5) [6,33,80,160,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2304
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2305 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 84 168 274 40 77 141 269), lower := (rows 7 35 84 168 274 40 64 128 256), losses := [] }

theorem u2305 : Upper (D 5) (R 5) [6,33,80,160,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2305
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2306 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 168 280 33 78 142 270), lower := (rows 7 35 84 168 280 33 64 128 256), losses := [] }

theorem u2306 : Upper (D 5) (R 5) [6,33,80,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2306
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2307 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 168 280 34 77 141 269), lower := (rows 7 35 84 168 280 34 64 128 256), losses := [] }

theorem u2307 : Upper (D 5) (R 5) [6,33,80,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2307
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2308 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 84 168 280 36 75 139 267), lower := (rows 7 35 84 168 280 36 64 128 256), losses := [] }

theorem u2308 : Upper (D 5) (R 5) [6,33,80,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2308
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2309 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 84 168 280 40 71 135 263), lower := (rows 7 35 84 168 280 40 64 128 256), losses := [] }

theorem u2309 : Upper (D 5) (R 5) [6,33,80,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2309
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2310 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 392 26 33 108 172 300), lower := (rows 7 35 84 392 26 33 64 128 256), losses := [] }

theorem u2310 : Upper (D 5) (R 5) [6,33,80,384,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2310
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2311 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 408, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 84 392 26 36 105 169 297), lower := (rows 7 35 84 392 26 36 64 128 256), losses := [] }

theorem u2311 : Upper (D 5) (R 5) [6,33,80,384,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2311
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2312 : Route 9 := (fun mask => (mask,id))

def c2312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2312 : Upper (D 5) (R 5) [6,33,80,384,10,8] 13 := by
  apply FastRouting.sound _ _ [6,33,80,384,10,8] 13 (by decide) (choices 1) [1,4,32] r2312 c2312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u432
  · exact u433
  · exact u434

def b2313 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 392 56 33 78 142 270), lower := (rows 7 35 84 392 56 33 64 128 256), losses := [] }

theorem u2313 : Upper (D 5) (R 5) [6,33,80,384,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2313
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2314 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 392 56 34 77 141 269), lower := (rows 7 35 84 392 56 34 64 128 256), losses := [] }

theorem u2314 : Upper (D 5) (R 5) [6,33,80,384,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2314
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2315 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 35 84 392 56 36 75 139 267), lower := (rows 7 35 84 392 56 36 64 128 256), losses := [] }

theorem u2315 : Upper (D 5) (R 5) [6,33,80,384,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2315
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2316 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 84 392 56 40 71 135 263), lower := (rows 7 35 84 392 56 40 64 128 256), losses := [] }

theorem u2316 : Upper (D 5) (R 5) [6,33,80,384,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2316
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2317 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 25 276 34 104 168 296), lower := (rows 7 35 196 25 276 34 64 128 256), losses := [] }

theorem u2317 : Upper (D 5) (R 5) [6,33,192,17,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2317
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2318 : Route 9 := (fun mask => (mask,id))

def c2318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2318 : Upper (D 5) (R 5) [6,33,192,17,260,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,260,8] 13 (by decide) (choices 1) [2,8,32] r2318 c2318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u435
  · exact u436
  · exact u437

def b2319 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 25 280 34 108 172 300), lower := (rows 7 35 196 25 280 34 64 128 256), losses := [] }

theorem u2319 : Upper (D 5) (R 5) [6,33,192,17,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2319
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2320 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 25 280 36 106 170 298), lower := (rows 7 35 196 25 280 36 64 128 256), losses := [] }

theorem u2320 : Upper (D 5) (R 5) [6,33,192,17,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2320
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2321 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 25 280 40 102 166 294), lower := (rows 7 35 196 25 280 40 64 128 256), losses := [] }

theorem u2321 : Upper (D 5) (R 5) [6,33,192,17,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2321
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2322 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 25 304 34 76 140 268), lower := (rows 7 35 196 25 304 34 64 128 256), losses := [] }

theorem u2322 : Upper (D 5) (R 5) [6,33,192,17,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2322
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2323 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 25 304 36 74 138 266), lower := (rows 7 35 196 25 304 36 64 128 256), losses := [] }

theorem u2323 : Upper (D 5) (R 5) [6,33,192,17,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2323
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2324 : Route 9 := (fun mask => (mask,id))

def c2324 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2324 : Upper (D 5) (R 5) [6,33,192,17,288,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,288,8] 13 (by decide) (choices 1) [2,4,8] r2324 c2324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u438
  · exact u439
  · exact u440

def b2325 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 26 276 33 104 168 296), lower := (rows 7 35 196 26 276 33 64 128 256), losses := [] }

theorem u2325 : Upper (D 5) (R 5) [6,33,192,18,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2325
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2326 : Route 9 := (fun mask => (mask,id))

def c2326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2326 : Upper (D 5) (R 5) [6,33,192,18,260,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,260,8] 13 (by decide) (choices 1) [1,8,32] r2326 c2326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u441
  · exact u442
  · exact u443

def b2327 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 26 280 33 108 172 300), lower := (rows 7 35 196 26 280 33 64 128 256), losses := [] }

theorem u2327 : Upper (D 5) (R 5) [6,33,192,18,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2327
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2328 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 26 280 36 105 169 297), lower := (rows 7 35 196 26 280 36 64 128 256), losses := [] }

theorem u2328 : Upper (D 5) (R 5) [6,33,192,18,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2328
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2329 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 26 280 40 101 165 293), lower := (rows 7 35 196 26 280 40 64 128 256), losses := [] }

theorem u2329 : Upper (D 5) (R 5) [6,33,192,18,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2329
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2330 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 28 273 34 104 168 296), lower := (rows 7 35 196 28 273 34 64 128 256), losses := [] }

theorem u2330 : Upper (D 5) (R 5) [6,33,192,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2330
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2331 : Route 9 := (fun mask => (mask,id))

def c2331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2331 : Upper (D 5) (R 5) [6,33,192,20,257,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,257,8] 13 (by decide) (choices 1) [2,8,32] r2331 c2331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u444
  · exact u445
  · exact u446

def b2332 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 28 274 33 104 168 296), lower := (rows 7 35 196 28 274 33 64 128 256), losses := [] }

theorem u2332 : Upper (D 5) (R 5) [6,33,192,20,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2332
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2333 : Route 9 := (fun mask => (mask,id))

def c2333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2333 : Upper (D 5) (R 5) [6,33,192,20,258,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,258,8] 13 (by decide) (choices 1) [1,8,32] r2333 c2333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u447
  · exact u448
  · exact u449

def b2334 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 28 280 33 106 170 298), lower := (rows 7 35 196 28 280 33 64 128 256), losses := [] }

theorem u2334 : Upper (D 5) (R 5) [6,33,192,20,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2334
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2335 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 28 280 34 105 169 297), lower := (rows 7 35 196 28 280 34 64 128 256), losses := [] }

theorem u2335 : Upper (D 5) (R 5) [6,33,192,20,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2335
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2336 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 28 280 40 99 163 291), lower := (rows 7 35 196 28 280 40 64 128 256), losses := [] }

theorem u2336 : Upper (D 5) (R 5) [6,33,192,20,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2336
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2337 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 28 304 33 74 138 266), lower := (rows 7 35 196 28 304 33 64 128 256), losses := [] }

theorem u2337 : Upper (D 5) (R 5) [6,33,192,20,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2337
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2338 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 28 304 34 73 137 265), lower := (rows 7 35 196 28 304 34 64 128 256), losses := [] }

theorem u2338 : Upper (D 5) (R 5) [6,33,192,20,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2338
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2339 : Route 9 := (fun mask => (mask,id))

def c2339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2339 : Upper (D 5) (R 5) [6,33,192,20,288,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,288,8] 13 (by decide) (choices 1) [1,2,8] r2339 c2339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u450
  · exact u451
  · exact u452

#print axioms u2339
end Delivery.IrregularNine14.P05
