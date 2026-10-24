import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0032
import IrregularNine14P05C0033

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5280 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 196 44 49 298 330 394 266), lower := (rows 7 19 196 44 49 32 64 128 256), losses := [] }

theorem u5280 : Upper (D 5) (R 5) [6,17,192,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5280
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5281 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 196 44 50 297 329 393 265), lower := (rows 7 19 196 44 50 32 64 128 256), losses := [] }

theorem u5281 : Upper (D 5) (R 5) [6,17,192,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5281
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5282 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 44 56 299 331 395 267), lower := (rows 7 19 196 44 56 32 64 128 256), losses := [] }

theorem u5282 : Upper (D 5) (R 5) [6,17,192,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5282
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5283 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 44 273 42 106 170 298), lower := (rows 7 19 196 44 273 32 64 128 256), losses := [] }

theorem u5283 : Upper (D 5) (R 5) [6,17,192,36,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5283
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5284 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 196 44 274 41 105 169 297), lower := (rows 7 19 196 44 274 32 64 128 256), losses := [] }

theorem u5284 : Upper (D 5) (R 5) [6,17,192,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5284
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5285 : Route 9 := (fun mask => (mask,id))

def c5285 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5285 : Upper (D 5) (R 5) [6,17,192,36,264] 13 := by
  apply FastRouting.sound _ _ [6,17,192,36,264] 13 (by decide) (choices 1) [1,2,8] r5285 c5285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1970
  · exact u1971
  · exact u1972

def r5286 : Route 9 := (fun mask => (mask,id))

def c5286 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5286 : Upper (D 5) (R 5) [6,17,192,36,288] 13 := by
  apply FastRouting.sound _ _ [6,17,192,36,288] 13 (by decide) (choices 1) [1,2,8] r5286 c5286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1973
  · exact u1974
  · exact u1975

def b5287 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 265 22 40 104 168 296), lower := (rows 7 19 196 265 22 32 64 128 256), losses := [] }

theorem u5287 : Upper (D 5) (R 5) [6,17,192,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5287
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5288 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 19 196 265 26 44 108 172 300), lower := (rows 7 19 196 265 26 32 64 128 256), losses := [] }

theorem u5288 : Upper (D 5) (R 5) [6,17,192,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5288
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5289 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 265 28 42 106 170 298), lower := (rows 7 19 196 265 28 32 64 128 256), losses := [] }

theorem u5289 : Upper (D 5) (R 5) [6,17,192,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5289
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5290 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 196 265 50 44 108 172 300), lower := (rows 7 19 196 265 50 32 64 128 256), losses := [] }

theorem u5290 : Upper (D 5) (R 5) [6,17,192,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5290
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5291 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 265 52 42 106 170 298), lower := (rows 7 19 196 265 52 32 64 128 256), losses := [] }

theorem u5291 : Upper (D 5) (R 5) [6,17,192,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5291
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5292 : Route 9 := (fun mask => (mask,id))

def c5292 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5292 : Upper (D 5) (R 5) [6,17,192,257,40] 13 := by
  apply FastRouting.sound _ _ [6,17,192,257,40] 13 (by decide) (choices 1) [2,4,8] r5292 c5292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1976
  · exact u1977
  · exact u1978

def b5293 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 266 21 40 104 168 296), lower := (rows 7 19 196 266 21 32 64 128 256), losses := [] }

theorem u5293 : Upper (D 5) (R 5) [6,17,192,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5293
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5294 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 266 25 44 108 172 300), lower := (rows 7 19 196 266 25 32 64 128 256), losses := [] }

theorem u5294 : Upper (D 5) (R 5) [6,17,192,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5294
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5295 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 266 28 41 105 169 297), lower := (rows 7 19 196 266 28 32 64 128 256), losses := [] }

theorem u5295 : Upper (D 5) (R 5) [6,17,192,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5295
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5296 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 266 49 44 108 172 300), lower := (rows 7 19 196 266 49 32 64 128 256), losses := [] }

theorem u5296 : Upper (D 5) (R 5) [6,17,192,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5296
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5297 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 266 52 41 105 169 297), lower := (rows 7 19 196 266 52 32 64 128 256), losses := [] }

theorem u5297 : Upper (D 5) (R 5) [6,17,192,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5297
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5298 : Route 9 := (fun mask => (mask,id))

def c5298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5298 : Upper (D 5) (R 5) [6,17,192,258,40] 13 := by
  apply FastRouting.sound _ _ [6,17,192,258,40] 13 (by decide) (choices 1) [1,4,8] r5298 c5298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1979
  · exact u1980
  · exact u1981

def b5299 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 268 19 40 104 168 296), lower := (rows 7 19 196 268 19 32 64 128 256), losses := [] }

theorem u5299 : Upper (D 5) (R 5) [6,17,192,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5299
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5300 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 196 268 25 42 106 170 298), lower := (rows 7 19 196 268 25 32 64 128 256), losses := [] }

theorem u5300 : Upper (D 5) (R 5) [6,17,192,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5300
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5301 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 196 268 26 41 105 169 297), lower := (rows 7 19 196 268 26 32 64 128 256), losses := [] }

theorem u5301 : Upper (D 5) (R 5) [6,17,192,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5301
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5302 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 268 49 42 106 170 298), lower := (rows 7 19 196 268 49 32 64 128 256), losses := [] }

theorem u5302 : Upper (D 5) (R 5) [6,17,192,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5302
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5303 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 196 268 50 41 105 169 297), lower := (rows 7 19 196 268 50 32 64 128 256), losses := [] }

theorem u5303 : Upper (D 5) (R 5) [6,17,192,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5303
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5304 : Route 9 := (fun mask => (mask,id))

def c5304 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5304 : Upper (D 5) (R 5) [6,17,192,260,40] 13 := by
  apply FastRouting.sound _ _ [6,17,192,260,40] 13 (by decide) (choices 1) [1,2,8] r5304 c5304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1982
  · exact u1983
  · exact u1984

def b5305 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 296 19 44 108 172 300), lower := (rows 7 19 196 296 19 32 64 128 256), losses := [] }

theorem u5305 : Upper (D 5) (R 5) [6,17,192,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5305
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5306 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 296 21 42 106 170 298), lower := (rows 7 19 196 296 21 32 64 128 256), losses := [] }

theorem u5306 : Upper (D 5) (R 5) [6,17,192,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5306
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5307 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 296 22 41 105 169 297), lower := (rows 7 19 196 296 22 32 64 128 256), losses := [] }

theorem u5307 : Upper (D 5) (R 5) [6,17,192,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5307
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5308 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 296 25 46 110 174 302), lower := (rows 7 19 196 296 25 32 64 128 256), losses := [] }

theorem u5308 : Upper (D 5) (R 5) [6,17,192,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5308
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5309 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 196 296 26 45 109 173 301), lower := (rows 7 19 196 296 26 32 64 128 256), losses := [] }

theorem u5309 : Upper (D 5) (R 5) [6,17,192,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5309
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5310 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 296 28 43 107 171 299), lower := (rows 7 19 196 296 28 32 64 128 256), losses := [] }

theorem u5310 : Upper (D 5) (R 5) [6,17,192,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5310
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5311 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 196 296 49 46 78 142 270), lower := (rows 7 19 196 296 49 32 64 128 256), losses := [] }

theorem u5311 : Upper (D 5) (R 5) [6,17,192,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5311
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5312 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 196 296 50 45 77 141 269), lower := (rows 7 19 196 296 50 32 64 128 256), losses := [] }

theorem u5312 : Upper (D 5) (R 5) [6,17,192,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5312
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5313 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 196 296 52 43 75 139 267), lower := (rows 7 19 196 296 52 32 64 128 256), losses := [] }

theorem u5313 : Upper (D 5) (R 5) [6,17,192,288,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5313
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5314 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 196 296 56 47 79 143 271), lower := (rows 7 19 196 296 56 32 64 128 256), losses := [] }

theorem u5314 : Upper (D 5) (R 5) [6,17,192,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5314
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5315 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 73 22 424 488 424 424), lower := (rows 7 26 37 73 22 32 64 128 256), losses := [] }

theorem u5315 : Upper (D 5) (R 5) [6,24,33,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5315
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5316 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 73 26 420 484 420 420), lower := (rows 7 26 37 73 26 32 64 128 256), losses := [] }

theorem u5316 : Upper (D 5) (R 5) [6,24,33,65,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5316
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5317 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 421, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 37 73 28 418 482 418 418), lower := (rows 7 26 37 73 28 32 64 128 256), losses := [] }

theorem u5317 : Upper (D 5) (R 5) [6,24,33,65,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5317
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5318 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 73 50 428 460 396 396), lower := (rows 7 26 37 73 50 32 64 128 256), losses := [] }

theorem u5318 : Upper (D 5) (R 5) [6,24,33,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5318
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5319 : PairBound 9 := { available := 394, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 26 37 73 52 426 458 394 394), lower := (rows 7 26 37 73 52 32 64 128 256), losses := [] }

theorem u5319 : Upper (D 5) (R 5) [6,24,33,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5319
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5320 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 73 56 422 454 390 390), lower := (rows 7 26 37 73 56 32 64 128 256), losses := [] }

theorem u5320 : Upper (D 5) (R 5) [6,24,33,65,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5320
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5321 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 73 146 300 364 428 300), lower := (rows 7 26 37 73 146 32 64 128 256), losses := [] }

theorem u5321 : Upper (D 5) (R 5) [6,24,33,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5321
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5322 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 360, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 7 26 37 73 148 298 362 426 298), lower := (rows 7 26 37 73 148 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 42 74 138 266), good := (rows 502 506 52 506 148 32 64 128 256) }] }

theorem u5322 : Upper (D 5) (R 5) [6,24,33,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5322
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5323 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 73 152 294 358 422 294), lower := (rows 7 26 37 73 152 32 64 128 256), losses := [] }

theorem u5323 : Upper (D 5) (R 5) [6,24,33,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5323
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5324 : Route 9 := (fun mask => (mask,id))

def c5324 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5324 : Upper (D 5) (R 5) [6,24,33,65,160] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,160] 13 (by decide) (choices 1) [2,4,8,256] r5324 c5324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1985
  · exact u1986
  · exact u1987
  · exact u1988

def r5325 : Route 9 := (fun mask => (mask,id))

def c5325 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5325 : Upper (D 5) (R 5) [6,24,33,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,384] 13 (by decide) (choices 1) [2,4,8] r5325 c5325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1989
  · exact u1990
  · exact u1991

def b5326 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 490, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 74 21 424 488 424 424), lower := (rows 7 26 37 74 21 32 64 128 256), losses := [] }

theorem u5326 : Upper (D 5) (R 5) [6,24,33,66,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5326
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5327 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 74 25 420 484 420 420), lower := (rows 7 26 37 74 25 32 64 128 256), losses := [] }

theorem u5327 : Upper (D 5) (R 5) [6,24,33,66,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5327
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5328 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 420, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 37 74 28 417 481 417 417), lower := (rows 7 26 37 74 28 32 64 128 256), losses := [] }

theorem u5328 : Upper (D 5) (R 5) [6,24,33,66,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5328
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5329 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 37 74 49 428 460 396 396), lower := (rows 7 26 37 74 49 32 64 128 256), losses := [] }

theorem u5329 : Upper (D 5) (R 5) [6,24,33,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5329
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5330 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 26 37 74 52 425 457 393 393), lower := (rows 7 26 37 74 52 32 64 128 256), losses := [] }

theorem u5330 : Upper (D 5) (R 5) [6,24,33,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5330
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5331 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 74 56 421 453 389 389), lower := (rows 7 26 37 74 56 32 64 128 256), losses := [] }

theorem u5331 : Upper (D 5) (R 5) [6,24,33,66,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5331
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5332 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 360, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 74 145 300 364 428 300), lower := (rows 7 26 37 74 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 25 16 37 69 133 261), good := (rows 494 26 492 74 506 32 64 128 256) }] }

theorem u5332 : Upper (D 5) (R 5) [6,24,33,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5332
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5333 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 360, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 37 74 148 297 361 425 297), lower := (rows 7 26 37 74 148 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 25 16 37 69 133 261), good := (rows 491 26 489 74 506 32 64 128 256) }] }

theorem u5333 : Upper (D 5) (R 5) [6,24,33,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5333
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5334 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 74 152 293 357 421 293), lower := (rows 7 26 37 74 152 32 64 128 256), losses := [] }

theorem u5334 : Upper (D 5) (R 5) [6,24,33,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5334
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5335 : Route 9 := (fun mask => (mask,id))

def c5335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5335 : Upper (D 5) (R 5) [6,24,33,66,160] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66,160] 13 (by decide) (choices 1) [1,4,8,256] r5335 c5335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1992
  · exact u1993
  · exact u1994
  · exact u1995

def r5336 : Route 9 := (fun mask => (mask,id))

def c5336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5336 : Upper (D 5) (R 5) [6,24,33,66,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66,384] 13 (by decide) (choices 1) [1,4,8] r5336 c5336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1996
  · exact u1997
  · exact u1998

def b5337 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 37 76 19 424 488 424 424), lower := (rows 7 26 37 76 19 32 64 128 256), losses := [] }

theorem u5337 : Upper (D 5) (R 5) [6,24,33,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5337
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5338 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 37 76 25 418 482 418 418), lower := (rows 7 26 37 76 25 32 64 128 256), losses := [] }

theorem u5338 : Upper (D 5) (R 5) [6,24,33,68,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5338
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5339 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 76 26 417 481 417 417), lower := (rows 7 26 37 76 26 32 64 128 256), losses := [] }

theorem u5339 : Upper (D 5) (R 5) [6,24,33,68,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5339
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5339
end Delivery.IrregularNine14.P05
