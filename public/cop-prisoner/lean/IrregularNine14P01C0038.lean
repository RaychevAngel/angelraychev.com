import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0007

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2280 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 266 100 168 17 242 210 210 466), lower := (rows 23 266 100 168 17 32 64 128 256), losses := [] }

theorem u2280 : Upper (D 1) (R 1) [22,264,96,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2280
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2281 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 266 100 168 18 241 209 209 465), lower := (rows 23 266 100 168 18 32 64 128 256), losses := [] }

theorem u2281 : Upper (D 1) (R 1) [22,264,96,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2281
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2282 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 266 100 168 80 179 211 147 403), lower := (rows 23 266 100 168 80 32 64 128 256), losses := [] }

theorem u2282 : Upper (D 1) (R 1) [22,264,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2282
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2283 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 23 266 100 168 144 115 83 211 339), lower := (rows 23 266 100 168 144 32 64 128 256), losses := [] }

theorem u2283 : Upper (D 1) (R 1) [22,264,96,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2283
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2284 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 13 74 48 240 208 208 464), lower := (rows 23 290 13 74 48 32 64 128 256), losses := [] }

theorem u2284 : Upper (D 1) (R 1) [22,288,9,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2284
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2285 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 21, targets := 32 }], pairs := [(0,5)], upper := (rows 23 290 13 74 80 176 240 176 432), lower := (rows 23 290 13 74 80 32 64 128 256), losses := [] }

theorem u2285 : Upper (D 1) (R 1) [22,288,9,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2285
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2286 : Route 9 := (fun mask => (mask,id))

def c2286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2286 : Upper (D 1) (R 1) [22,288,9,66,128] 13 := by
  apply FastRouting.sound _ _ [22,288,9,66,128] 13 (by decide) (choices 1) [16,64,128] r2286 c2286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u430
  · exact u431
  · exact u432

def b2287 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 13 104 18 240 208 208 464), lower := (rows 23 290 13 104 18 32 64 128 256), losses := [] }

theorem u2287 : Upper (D 1) (R 1) [22,288,9,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2287
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2288 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 13 104 80 178 210 146 402), lower := (rows 23 290 13 104 80 32 64 128 256), losses := [] }

theorem u2288 : Upper (D 1) (R 1) [22,288,9,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2288
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2289 : Route 9 := (fun mask => (mask,id))

def c2289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2289 : Upper (D 1) (R 1) [22,288,9,96,128] 13 := by
  apply FastRouting.sound _ _ [22,288,9,96,128] 13 (by decide) (choices 1) [2,16,64,128] r2289 c2289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u433
  · exact u434
  · exact u435
  · exact u436

def b2290 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 13 200 18 240 240 240 496), lower := (rows 23 290 13 200 18 32 64 128 256), losses := [] }

theorem u2290 : Upper (D 1) (R 1) [22,288,9,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2290
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2291 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 13 200 48 242 210 210 466), lower := (rows 23 290 13 200 48 32 64 128 256), losses := [] }

theorem u2291 : Upper (D 1) (R 1) [22,288,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2291
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2292 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 13 200 80 178 242 178 434), lower := (rows 23 290 13 200 80 32 64 128 256), losses := [] }

theorem u2292 : Upper (D 1) (R 1) [22,288,9,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2292
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2293 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 23 290 69 138 24 240 240 240 496), lower := (rows 23 290 69 138 24 32 64 128 256), losses := [] }

theorem u2293 : Upper (D 1) (R 1) [22,288,65,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2293
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2294 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 69 138 48 248 216 216 472), lower := (rows 23 290 69 138 48 32 64 128 256), losses := [] }

theorem u2294 : Upper (D 1) (R 1) [22,288,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2294
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2295 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 69 138 80 184 248 184 440), lower := (rows 23 290 69 138 80 32 64 128 256), losses := [] }

theorem u2295 : Upper (D 1) (R 1) [22,288,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2296 : Route 9 := (fun mask => (mask,id))

def c2296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2296 : Upper (D 1) (R 1) [22,288,65,130,128] 13 := by
  apply FastRouting.sound _ _ [22,288,65,130,128] 13 (by decide) (choices 1) [8,16,64] r2296 c2296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u437
  · exact u438
  · exact u439

def b2297 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 69 168 18 248 216 216 472), lower := (rows 23 290 69 168 18 32 64 128 256), losses := [] }

theorem u2297 : Upper (D 1) (R 1) [22,288,65,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2297
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2298 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 290 69 168 24 242 210 210 466), lower := (rows 23 290 69 168 24 32 64 128 256), losses := [] }

theorem u2298 : Upper (D 1) (R 1) [22,288,65,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2298
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2299 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 69 168 80 186 218 154 410), lower := (rows 23 290 69 168 80 32 64 128 256), losses := [] }

theorem u2299 : Upper (D 1) (R 1) [22,288,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2299
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2300 : Route 9 := (fun mask => (mask,id))

def c2300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2300 : Upper (D 1) (R 1) [22,288,65,160,128] 13 := by
  apply FastRouting.sound _ _ [22,288,65,160,128] 13 (by decide) (choices 1) [2,8,16,64] r2300 c2300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u440
  · exact u441
  · exact u442
  · exact u443

def b2301 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 76 137 18 240 240 240 496), lower := (rows 23 290 76 137 18 32 64 128 256), losses := [] }

theorem u2301 : Upper (D 1) (R 1) [22,288,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2302 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 76 137 48 242 210 210 466), lower := (rows 23 290 76 137 48 32 64 128 256), losses := [] }

theorem u2302 : Upper (D 1) (R 1) [22,288,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2302
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2303 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 76 137 80 178 242 178 434), lower := (rows 23 290 76 137 80 32 64 128 256), losses := [] }

theorem u2303 : Upper (D 1) (R 1) [22,288,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2303
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2304 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 23 290 76 137 144 114 114 242 370), lower := (rows 23 290 76 137 144 32 64 128 256), losses := [] }

theorem u2304 : Upper (D 1) (R 1) [22,288,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2304
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2305 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 23 290 76 138 17 240 240 240 496), lower := (rows 23 290 76 138 17 32 64 128 256), losses := [] }

theorem u2305 : Upper (D 1) (R 1) [22,288,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2305
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2306 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 76 138 48 241 209 209 465), lower := (rows 23 290 76 138 48 32 64 128 256), losses := [] }

theorem u2306 : Upper (D 1) (R 1) [22,288,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2307 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 76 138 80 177 241 177 433), lower := (rows 23 290 76 138 80 32 64 128 256), losses := [] }

theorem u2307 : Upper (D 1) (R 1) [22,288,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2307
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2308 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 23 290 76 138 144 113 113 241 369), lower := (rows 23 290 76 138 144 32 64 128 256), losses := [] }

theorem u2308 : Upper (D 1) (R 1) [22,288,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2308
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2309 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 290 76 168 17 242 210 210 466), lower := (rows 23 290 76 168 17 32 64 128 256), losses := [] }

theorem u2309 : Upper (D 1) (R 1) [22,288,72,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2309
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2310 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 76 168 18 241 209 209 465), lower := (rows 23 290 76 168 18 32 64 128 256), losses := [] }

theorem u2310 : Upper (D 1) (R 1) [22,288,72,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2310
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2311 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 76 168 80 179 211 147 403), lower := (rows 23 290 76 168 80 32 64 128 256), losses := [] }

theorem u2311 : Upper (D 1) (R 1) [22,288,72,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2311
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2312 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 23 290 76 168 144 115 83 211 339), lower := (rows 23 290 76 168 144 32 64 128 256), losses := [] }

theorem u2312 : Upper (D 1) (R 1) [22,288,72,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2312
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2313 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 196 41 18 248 216 216 472), lower := (rows 23 290 196 41 18 32 64 128 256), losses := [] }

theorem u2313 : Upper (D 1) (R 1) [22,288,192,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2313
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2314 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 23 290 196 41 24 242 210 210 466), lower := (rows 23 290 196 41 24 32 64 128 256), losses := [] }

theorem u2314 : Upper (D 1) (R 1) [22,288,192,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2314
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2315 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 196 41 80 186 218 154 410), lower := (rows 23 290 196 41 80 32 64 128 256), losses := [] }

theorem u2315 : Upper (D 1) (R 1) [22,288,192,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2315
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2316 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 23 290 196 56 17 234 202 202 458), lower := (rows 23 290 196 56 17 32 64 128 256), losses := [] }

theorem u2316 : Upper (D 1) (R 1) [22,288,192,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2316
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2317 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 196 56 18 233 201 201 457), lower := (rows 23 290 196 56 18 32 64 128 256), losses := [] }

theorem u2317 : Upper (D 1) (R 1) [22,288,192,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2317
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2318 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 23 290 196 56 24 227 195 195 451), lower := (rows 23 290 196 56 24 32 64 128 256), losses := [] }

theorem u2318 : Upper (D 1) (R 1) [22,288,192,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2318
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2319 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 196 56 80 171 203 139 395), lower := (rows 23 290 196 56 80 32 64 128 256), losses := [] }

theorem u2319 : Upper (D 1) (R 1) [22,288,192,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2319
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2320 : PairBound 9 := { available := 184, camps := [], pairs := [], upper := (rows 23 290 196 74 17 184 248 184 440), lower := (rows 23 290 196 74 17 32 64 128 256), losses := [] }

theorem u2320 : Upper (D 1) (R 1) [22,288,192,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2320
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2321 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 23 290 196 74 24 177 241 177 433), lower := (rows 23 290 196 74 24 32 64 128 256), losses := [] }

theorem u2321 : Upper (D 1) (R 1) [22,288,192,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2321
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2322 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 196 74 48 185 217 153 409), lower := (rows 23 290 196 74 48 32 64 128 256), losses := [] }

theorem u2322 : Upper (D 1) (R 1) [22,288,192,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2322
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2323 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 290 196 74 144 57 121 185 313), lower := (rows 23 290 196 74 144 32 64 128 256), losses := [] }

theorem u2323 : Upper (D 1) (R 1) [22,288,192,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2323
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2324 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 23 290 196 88 17 170 234 170 426), lower := (rows 23 290 196 88 17 32 64 128 256), losses := [] }

theorem u2324 : Upper (D 1) (R 1) [22,288,192,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2324
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2325 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 196 88 18 169 233 169 425), lower := (rows 23 290 196 88 18 32 64 128 256), losses := [] }

theorem u2325 : Upper (D 1) (R 1) [22,288,192,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2325
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2326 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 23 290 196 88 24 163 227 163 419), lower := (rows 23 290 196 88 24 32 64 128 256), losses := [] }

theorem u2326 : Upper (D 1) (R 1) [22,288,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2326
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2327 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 23 290 196 88 48 171 203 139 395), lower := (rows 23 290 196 88 48 32 64 128 256), losses := [] }

theorem u2327 : Upper (D 1) (R 1) [22,288,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2327
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2328 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 290 196 88 144 43 107 171 299), lower := (rows 23 290 196 88 144 32 64 128 256), losses := [] }

theorem u2328 : Upper (D 1) (R 1) [22,288,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2328
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2329 : PairBound 9 := { available := 154, camps := [], pairs := [], upper := (rows 23 290 196 104 17 186 218 154 410), lower := (rows 23 290 196 104 17 32 64 128 256), losses := [] }

theorem u2329 : Upper (D 1) (R 1) [22,288,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2329
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2330 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 23 290 196 104 18 185 217 153 409), lower := (rows 23 290 196 104 18 32 64 128 256), losses := [] }

theorem u2330 : Upper (D 1) (R 1) [22,288,192,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2330
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2331 : PairBound 9 := { available := 147, camps := [], pairs := [], upper := (rows 23 290 196 104 24 179 211 147 403), lower := (rows 23 290 196 104 24 32 64 128 256), losses := [] }

theorem u2331 : Upper (D 1) (R 1) [22,288,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2332 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 290 196 104 144 59 91 155 283), lower := (rows 23 290 196 104 144 32 64 128 256), losses := [] }

theorem u2332 : Upper (D 1) (R 1) [22,288,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2332
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2333 : PairBound 9 := { available := 464, camps := [], pairs := [(2,5)], upper := (rows 29 35 70 138 48 496 464 464 464), lower := (rows 29 35 70 138 48 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 16 0 81 145 273), good := (rows 477 463 78 142 464 0 64 128 256) }] }

theorem u2333 : Upper (D 1) (R 1) [28,33,66,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2333
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2334 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 70 138 80 432 496 432 432), lower := (rows 29 35 70 138 80 32 64 128 256), losses := [] }

theorem u2334 : Upper (D 1) (R 1) [28,33,66,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2334
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2335 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 29 35 70 138 272 240 240 240 496), lower := (rows 29 35 70 138 272 32 64 128 256), losses := [] }

theorem u2335 : Upper (D 1) (R 1) [28,33,66,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2335
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2336 : PairBound 9 := { available := 208, camps := [], pairs := [(2,5)], upper := (rows 29 35 70 266 48 240 208 208 464), lower := (rows 29 35 70 266 48 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 10 16 0 81 145 273), good := (rows 477 463 78 270 464 0 64 128 256) }] }

theorem u2336 : Upper (D 1) (R 1) [28,33,66,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2336
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2337 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 70 266 80 176 240 176 432), lower := (rows 29 35 70 266 80 32 64 128 256), losses := [] }

theorem u2337 : Upper (D 1) (R 1) [28,33,66,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2337
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2338 : Route 9 := (fun mask => (mask,id))

def c2338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2338 : Upper (D 1) (R 1) [28,33,66,258,128] 13 := by
  apply FastRouting.sound _ _ [28,33,66,258,128] 13 (by decide) (choices 1) [16,64,128] r2338 c2338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u444
  · exact u445
  · exact u446

def b2339 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 29 35 70 392 18 240 240 240 496), lower := (rows 29 35 70 392 18 32 64 128 256), losses := [] }

theorem u2339 : Upper (D 1) (R 1) [28,33,66,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2339
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2339
end Delivery.IrregularNine14.P01
