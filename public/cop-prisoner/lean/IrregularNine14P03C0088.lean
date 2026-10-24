import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0034

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5280 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 76 145 177 209 145 401), lower := (rows 259 98 44 76 145 32 64 128 256), losses := [] }

theorem u5280 : Upper (D 3) (R 3) [258,96,40,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5280
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5281 : Route 9 := (fun mask => (mask,id))

def c5281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5281 : Upper (D 3) (R 3) [258,96,40,80,129] 13 := by
  apply FastRouting.sound _ _ [258,96,40,80,129] 13 (by decide) (choices 1) [1,4,128] r5281 c5281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2068
  · exact u2069
  · exact u2070

def b5282 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 44 88 148 161 193 129 385), lower := (rows 259 98 44 88 148 32 64 128 256), losses := [] }

theorem u5282 : Upper (D 3) (R 3) [258,96,40,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5282
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5283 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 44 137 145 117 85 213 341), lower := (rows 259 98 44 137 145 32 64 128 256), losses := [] }

theorem u5283 : Upper (D 3) (R 3) [258,96,40,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5283
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5284 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 137 148 113 81 209 337), lower := (rows 259 98 44 137 148 32 64 128 256), losses := [] }

theorem u5284 : Upper (D 3) (R 3) [258,96,40,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5284
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5285 : Route 9 := (fun mask => (mask,id))

def c5285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5285 : Upper (D 3) (R 3) [258,96,40,129,192] 13 := by
  apply FastRouting.sound _ _ [258,96,40,129,192] 13 (by decide) (choices 1) [1,4,16] r5285 c5285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2071
  · exact u2072
  · exact u2073

def b5286 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 44 140 145 113 81 209 337), lower := (rows 259 98 44 140 145 32 64 128 256), losses := [] }

theorem u5286 : Upper (D 3) (R 3) [258,96,40,132,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5286
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5287 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 44 140 208 49 81 145 273), lower := (rows 259 98 44 140 208 32 64 128 256), losses := [] }

theorem u5287 : Upper (D 3) (R 3) [258,96,40,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5287
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5288 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 152 145 101 69 197 325), lower := (rows 259 98 44 152 145 32 64 128 256), losses := [] }

theorem u5288 : Upper (D 3) (R 3) [258,96,40,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5288
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5289 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 152 148 97 65 193 321), lower := (rows 259 98 44 152 148 32 64 128 256), losses := [] }

theorem u5289 : Upper (D 3) (R 3) [258,96,40,144,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5289
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5290 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 152 208 37 69 133 261), lower := (rows 259 98 44 152 208 32 64 128 256), losses := [] }

theorem u5290 : Upper (D 3) (R 3) [258,96,40,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5290
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5291 : Route 9 := (fun mask => (mask,id))

def c5291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5291 : Upper (D 3) (R 3) [258,96,40,192,129] 13 := by
  apply FastRouting.sound _ _ [258,96,40,192,129] 13 (by decide) (choices 1) [1,4,16] r5291 c5291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2074
  · exact u2075
  · exact u2076

def b5292 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 200 148 49 81 145 273), lower := (rows 259 98 44 200 148 32 64 128 256), losses := [] }

theorem u5292 : Upper (D 3) (R 3) [258,96,40,192,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5292
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5293 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 100 137 148 57 89 153 281), lower := (rows 259 98 100 137 148 32 64 128 256), losses := [] }

theorem u5293 : Upper (D 3) (R 3) [258,96,96,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5293
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5294 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 25 88 224 224 224 480), lower := (rows 289 7 7 25 88 32 64 128 256), losses := [] }

theorem u5294 : Upper (D 3) (R 3) [288,5,3,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5294
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5295 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 25 208 232 232 232 488), lower := (rows 289 7 7 25 208 32 64 128 256), losses := [] }

theorem u5295 : Upper (D 3) (R 3) [288,5,3,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5295
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5296 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 56 81 232 200 200 456), lower := (rows 289 7 7 56 81 32 64 128 256), losses := [] }

theorem u5296 : Upper (D 3) (R 3) [288,5,3,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5296
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5297 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 56 208 233 201 201 457), lower := (rows 289 7 7 56 208 32 64 128 256), losses := [] }

theorem u5297 : Upper (D 3) (R 3) [288,5,3,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5297
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5298 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 73 112 184 216 152 408), lower := (rows 289 7 7 73 112 32 64 128 256), losses := [] }

theorem u5298 : Upper (D 3) (R 3) [288,5,3,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5298
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5299 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 73 152 240 240 240 496), lower := (rows 289 7 7 73 152 32 64 128 256), losses := [] }

theorem u5299 : Upper (D 3) (R 3) [288,5,3,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5299
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5300 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 73 176 248 216 216 472), lower := (rows 289 7 7 73 176 32 64 128 256), losses := [] }

theorem u5300 : Upper (D 3) (R 3) [288,5,3,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5300
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5301 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 73 208 184 248 184 440), lower := (rows 289 7 7 73 208 32 64 128 256), losses := [] }

theorem u5301 : Upper (D 3) (R 3) [288,5,3,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5301
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5302 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 88 152 225 225 225 481), lower := (rows 289 7 7 88 152 32 64 128 256), losses := [] }

theorem u5302 : Upper (D 3) (R 3) [288,5,3,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5302
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5303 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 88 176 233 201 201 457), lower := (rows 289 7 7 88 176 32 64 128 256), losses := [] }

theorem u5303 : Upper (D 3) (R 3) [288,5,3,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5303
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5304 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 104 208 185 217 153 409), lower := (rows 289 7 7 104 208 32 64 128 256), losses := [] }

theorem u5304 : Upper (D 3) (R 3) [288,5,3,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5304
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5305 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 25 82 224 224 224 480), lower := (rows 289 7 13 25 82 32 64 128 256), losses := [] }

theorem u5305 : Upper (D 3) (R 3) [288,5,9,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5305
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5306 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 25 208 226 226 226 482), lower := (rows 289 7 13 25 208 32 64 128 256), losses := [] }

theorem u5306 : Upper (D 3) (R 3) [288,5,9,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5306
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5307 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 26 81 224 224 224 480), lower := (rows 289 7 13 26 81 32 64 128 256), losses := [] }

theorem u5307 : Upper (D 3) (R 3) [288,5,9,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5307
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5308 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 13 26 112 225 193 193 449), lower := (rows 289 7 13 26 112 32 64 128 256), losses := [] }

theorem u5308 : Upper (D 3) (R 3) [288,5,9,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5308
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5309 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 26 208 225 225 225 481), lower := (rows 289 7 13 26 208 32 64 128 256), losses := [] }

theorem u5309 : Upper (D 3) (R 3) [288,5,9,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5309
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5310 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 13 42 81 240 208 208 464), lower := (rows 289 7 13 42 81 32 64 128 256), losses := [] }

theorem u5310 : Upper (D 3) (R 3) [288,5,9,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5310
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5311 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 13 42 208 241 209 209 465), lower := (rows 289 7 13 42 208 32 64 128 256), losses := [] }

theorem u5311 : Upper (D 3) (R 3) [288,5,9,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5311
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5312 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 56 81 226 194 194 450), lower := (rows 289 7 13 56 81 32 64 128 256), losses := [] }

theorem u5312 : Upper (D 3) (R 3) [288,5,9,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5312
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5313 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 56 82 225 193 193 449), lower := (rows 289 7 13 56 82 32 64 128 256), losses := [] }

theorem u5313 : Upper (D 3) (R 3) [288,5,9,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5313
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5314 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 56 208 227 195 195 451), lower := (rows 289 7 13 56 208 32 64 128 256), losses := [] }

theorem u5314 : Upper (D 3) (R 3) [288,5,9,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5314
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5315 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 73 50 240 208 208 464), lower := (rows 289 7 13 73 50 32 64 128 256), losses := [] }

theorem u5315 : Upper (D 3) (R 3) [288,5,9,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5315
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5316 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 73 82 176 240 176 432), lower := (rows 289 7 13 73 82 32 64 128 256), losses := [] }

theorem u5316 : Upper (D 3) (R 3) [288,5,9,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5316
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5317 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 73 112 178 210 146 402), lower := (rows 289 7 13 73 112 32 64 128 256), losses := [] }

theorem u5317 : Upper (D 3) (R 3) [288,5,9,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5317
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5318 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 73 146 240 240 240 496), lower := (rows 289 7 13 73 146 32 64 128 256), losses := [] }

theorem u5318 : Upper (D 3) (R 3) [288,5,9,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5318
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5319 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 73 176 242 210 210 466), lower := (rows 289 7 13 73 176 32 64 128 256), losses := [] }

theorem u5319 : Upper (D 3) (R 3) [288,5,9,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5319
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5320 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 73 208 178 242 178 434), lower := (rows 289 7 13 73 208 32 64 128 256), losses := [] }

theorem u5320 : Upper (D 3) (R 3) [288,5,9,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5320
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5321 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 81 176 240 176 432), lower := (rows 289 7 13 74 81 32 64 128 256), losses := [] }

theorem u5321 : Upper (D 3) (R 3) [288,5,9,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5321
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5322 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 112 177 209 145 401), lower := (rows 289 7 13 74 112 32 64 128 256), losses := [] }

theorem u5322 : Upper (D 3) (R 3) [288,5,9,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5322
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5323 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 145 240 240 240 496), lower := (rows 289 7 13 74 145 32 64 128 256), losses := [] }

theorem u5323 : Upper (D 3) (R 3) [288,5,9,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5323
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5324 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 176 241 209 209 465), lower := (rows 289 7 13 74 176 32 64 128 256), losses := [] }

theorem u5324 : Upper (D 3) (R 3) [288,5,9,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5324
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5325 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 208 177 241 177 433), lower := (rows 289 7 13 74 208 32 64 128 256), losses := [] }

theorem u5325 : Upper (D 3) (R 3) [288,5,9,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5325
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5326 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 13 88 50 225 193 193 449), lower := (rows 289 7 13 88 50 32 64 128 256), losses := [] }

theorem u5326 : Upper (D 3) (R 3) [288,5,9,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5326
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5327 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 88 145 226 226 226 482), lower := (rows 289 7 13 88 145 32 64 128 256), losses := [] }

theorem u5327 : Upper (D 3) (R 3) [288,5,9,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5327
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5328 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 88 146 225 225 225 481), lower := (rows 289 7 13 88 146 32 64 128 256), losses := [] }

theorem u5328 : Upper (D 3) (R 3) [288,5,9,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5328
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5329 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 13 88 176 227 195 195 451), lower := (rows 289 7 13 88 176 32 64 128 256), losses := [] }

theorem u5329 : Upper (D 3) (R 3) [288,5,9,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5329
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5330 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 81 178 210 146 402), lower := (rows 289 7 13 104 81 32 64 128 256), losses := [] }

theorem u5330 : Upper (D 3) (R 3) [288,5,9,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5330
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5331 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 82 177 209 145 401), lower := (rows 289 7 13 104 82 32 64 128 256), losses := [] }

theorem u5331 : Upper (D 3) (R 3) [288,5,9,96,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5331
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5332 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 145 242 210 210 466), lower := (rows 289 7 13 104 145 32 64 128 256), losses := [] }

theorem u5332 : Upper (D 3) (R 3) [288,5,9,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5332
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5333 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 146 241 209 209 465), lower := (rows 289 7 13 104 146 32 64 128 256), losses := [] }

theorem u5333 : Upper (D 3) (R 3) [288,5,9,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5333
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5334 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 208 179 211 147 403), lower := (rows 289 7 13 104 208 32 64 128 256), losses := [] }

theorem u5334 : Upper (D 3) (R 3) [288,5,9,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5334
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5335 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 200 50 241 209 209 465), lower := (rows 289 7 13 200 50 32 64 128 256), losses := [] }

theorem u5335 : Upper (D 3) (R 3) [288,5,9,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5335
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5336 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 200 81 178 242 178 434), lower := (rows 289 7 13 200 81 32 64 128 256), losses := [] }

theorem u5336 : Upper (D 3) (R 3) [288,5,9,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5336
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5337 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 200 82 177 241 177 433), lower := (rows 289 7 13 200 82 32 64 128 256), losses := [] }

theorem u5337 : Upper (D 3) (R 3) [288,5,9,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5337
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5338 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 200 112 179 211 147 403), lower := (rows 289 7 13 200 112 32 64 128 256), losses := [] }

theorem u5338 : Upper (D 3) (R 3) [288,5,9,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5338
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5339 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 25 81 224 224 224 480), lower := (rows 289 7 14 25 81 32 64 128 256), losses := [] }

theorem u5339 : Upper (D 3) (R 3) [288,5,10,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5339
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5339
end Delivery.IrregularNine14.P03
