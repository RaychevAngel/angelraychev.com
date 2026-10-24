import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0020

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10260 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 133 74 276 33 112 240 368), lower := (rows 7 42 133 74 276 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 37 80 144 272), good := (rows 35 42 161 74 506 33 64 128 256) }] }

theorem u10260 : Upper (D 6) (R 6) [6,40,129,66,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10260
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10261 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 42 133 74 276 48 97 225 353), lower := (rows 7 42 133 74 276 48 64 128 256), losses := [] }

theorem u10261 : Upper (D 6) (R 6) [6,40,129,66,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10261
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10262 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 74 276 96 113 177 305), lower := (rows 7 42 133 74 276 96 64 128 256), losses := [] }

theorem u10262 : Upper (D 6) (R 6) [6,40,129,66,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10262
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10263 : Route 9 := (fun mask => (mask,id))

def c10263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10263 : Upper (D 6) (R 6) [6,40,129,66,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,288,1] 13 (by decide) (choices 1) [4,16] r10263 c10263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1207
  · exact u1208

def r10264 : Route 9 := (fun mask => (mask,id))

def c10264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10264 : Upper (D 6) (R 6) [6,40,129,66,288,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,288,4] 13 (by decide) (choices 1) [1,16] r10264 c10264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1209
  · exact u1210

def b10265 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 133 74 304 48 69 197 325), lower := (rows 7 42 133 74 304 48 64 128 256), losses := [] }

theorem u10265 : Upper (D 6) (R 6) [6,40,129,66,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10265
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10266 : PairBound 9 := { available := 21, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 74 304 96 85 149 277), lower := (rows 7 42 133 74 304 96 64 128 256), losses := [] }

theorem u10266 : Upper (D 6) (R 6) [6,40,129,66,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10266
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10267 : Route 9 := (fun mask => (mask,id))

def c10267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10267 : Upper (D 6) (R 6) [6,40,129,66,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,320,1] 13 (by decide) (choices 1) [4,16,32] r10267 c10267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1211
  · exact u1212
  · exact u1213

def r10268 : Route 9 := (fun mask => (mask,id))

def c10268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10268 : Upper (D 6) (R 6) [6,40,129,66,320,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,320,4] 13 (by decide) (choices 1) [1,16,32] r10268 c10268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1214
  · exact u1215
  · exact u1216

def b10269 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 74 336 48 101 165 293), lower := (rows 7 42 133 74 336 48 64 128 256), losses := [] }

theorem u10269 : Upper (D 6) (R 6) [6,40,129,66,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10269
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10270 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 42 133 76 49 34 336 464 336), lower := (rows 7 42 133 76 49 34 64 128 256), losses := [] }

theorem u10270 : Upper (D 6) (R 6) [6,40,129,68,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10270
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10271 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 76 49 48 322 450 322), lower := (rows 7 42 133 76 49 48 64 128 256), losses := [] }

theorem u10271 : Upper (D 6) (R 6) [6,40,129,68,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10271
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10272 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 76 49 96 338 402 274), lower := (rows 7 42 133 76 49 96 64 128 256), losses := [] }

theorem u10272 : Upper (D 6) (R 6) [6,40,129,68,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10272
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10273 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 42 133 76 49 288 82 210 338), lower := (rows 7 42 133 76 49 288 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 21 319 73 137 265), good := (rows 499 490 497 506 497 288 64 128 288) }] }

theorem u10273 : Upper (D 6) (R 6) [6,40,129,68,33,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10273
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10274 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 133 76 81 34 368 432 304), lower := (rows 7 42 133 76 81 34 64 128 256), losses := [] }

theorem u10274 : Upper (D 6) (R 6) [6,40,129,68,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10274
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10275 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 42 133 76 81 48 354 418 290), lower := (rows 7 42 133 76 81 48 64 128 256), losses := [] }

theorem u10275 : Upper (D 6) (R 6) [6,40,129,68,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10275
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10276 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 42 133 76 81 288 114 178 306), lower := (rows 7 42 133 76 81 288 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 21 319 73 137 265), good := (rows 499 490 497 506 497 288 64 128 288) }] }

theorem u10276 : Upper (D 6) (R 6) [6,40,129,68,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10276
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10277 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 7 42 133 76 112 33 338 402 274), lower := (rows 7 42 133 76 112 33 64 128 256), losses := [] }

theorem u10277 : Upper (D 6) (R 6) [6,40,129,68,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10277
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10278 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 133 76 112 34 337 401 273), lower := (rows 7 42 133 76 112 34 64 128 256), losses := [] }

theorem u10278 : Upper (D 6) (R 6) [6,40,129,68,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10278
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10279 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 76 112 48 323 387 259), lower := (rows 7 42 133 76 112 48 64 128 256), losses := [] }

theorem u10279 : Upper (D 6) (R 6) [6,40,129,68,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10279
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10280 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 42 133 76 112 288 83 147 275), lower := (rows 7 42 133 76 112 288 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 29 293 65 129 257), good := (rows 499 58 497 122 112 288 64 128 288) }] }

theorem u10280 : Upper (D 6) (R 6) [6,40,129,68,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10280
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10281 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 133 76 273 34 112 240 368), lower := (rows 7 42 133 76 273 34 64 128 256), losses := [] }

theorem u10281 : Upper (D 6) (R 6) [6,40,129,68,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10281
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10282 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(4,2)], upper := (rows 7 42 133 76 273 48 98 226 354), lower := (rows 7 42 133 76 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 9 16 48 114 178 306), good := (rows 462 490 140 76 506 498 64 128 256) }] }

theorem u10282 : Upper (D 6) (R 6) [6,40,129,68,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10282
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10283 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 76 273 96 114 178 306), lower := (rows 7 42 133 76 273 96 64 128 256), losses := [] }

theorem u10283 : Upper (D 6) (R 6) [6,40,129,68,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10283
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10284 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 7 42 133 76 274 33 112 240 368), lower := (rows 7 42 133 76 274 33 64 128 256), losses := [] }

theorem u10284 : Upper (D 6) (R 6) [6,40,129,68,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10284
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10285 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 42 133 76 274 48 97 225 353), lower := (rows 7 42 133 76 274 48 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 63 69 133 261), good := (rows 499 58 497 506 306 48 64 128 256) }] }

theorem u10285 : Upper (D 6) (R 6) [6,40,129,68,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10285
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10286 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 76 274 96 113 177 305), lower := (rows 7 42 133 76 274 96 64 128 256), losses := [] }

theorem u10286 : Upper (D 6) (R 6) [6,40,129,68,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10286
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10287 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 7 42 133 76 304 33 82 210 338), lower := (rows 7 42 133 76 304 33 64 128 256), losses := [] }

theorem u10287 : Upper (D 6) (R 6) [6,40,129,68,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10287
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10288 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 133 76 304 34 81 209 337), lower := (rows 7 42 133 76 304 34 64 128 256), losses := [] }

theorem u10288 : Upper (D 6) (R 6) [6,40,129,68,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10288
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10289 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 133 76 304 48 67 195 323), lower := (rows 7 42 133 76 304 48 64 128 256), losses := [] }

theorem u10289 : Upper (D 6) (R 6) [6,40,129,68,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10289
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10290 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 76 304 96 83 147 275), lower := (rows 7 42 133 76 304 96 64 128 256), losses := [] }

theorem u10290 : Upper (D 6) (R 6) [6,40,129,68,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10290
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10291 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 7 42 133 76 336 33 114 178 306), lower := (rows 7 42 133 76 336 33 64 128 256), losses := [] }

theorem u10291 : Upper (D 6) (R 6) [6,40,129,68,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10291
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10292 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 133 76 336 34 113 177 305), lower := (rows 7 42 133 76 336 34 64 128 256), losses := [] }

theorem u10292 : Upper (D 6) (R 6) [6,40,129,68,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10292
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10293 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 42 133 76 336 48 99 163 291), lower := (rows 7 42 133 76 336 48 64 128 256), losses := [] }

theorem u10293 : Upper (D 6) (R 6) [6,40,129,68,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10293
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10294 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 330, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 88 52 33 322 450 322), lower := (rows 7 42 133 88 52 33 64 128 256), losses := [] }

theorem u10294 : Upper (D 6) (R 6) [6,40,129,80,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10294
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10295 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 88 52 34 321 449 321), lower := (rows 7 42 133 88 52 34 64 128 256), losses := [] }

theorem u10295 : Upper (D 6) (R 6) [6,40,129,80,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10295
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10296 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 88 52 96 323 387 259), lower := (rows 7 42 133 88 52 96 64 128 256), losses := [] }

theorem u10296 : Upper (D 6) (R 6) [6,40,129,80,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10296
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10297 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 88 52 288 67 195 323), lower := (rows 7 42 133 88 52 288 64 128 256), losses := [] }

theorem u10297 : Upper (D 6) (R 6) [6,40,129,80,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10297
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10298 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 88 273 34 100 228 356), lower := (rows 7 42 133 88 273 34 64 128 256), losses := [] }

theorem u10298 : Upper (D 6) (R 6) [6,40,129,80,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10298
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10299 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(3,0),(3,2)], upper := (rows 7 42 133 88 273 36 98 226 354), lower := (rows 7 42 133 88 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 83 147 275), good := (rows 486 490 484 474 506 36 64 128 256) },{ target := 2, region := (rows 1 2 0 9 17 32 66 130 258), good := (rows 475 490 153 88 281 32 64 128 256) }] }

theorem u10299 : Upper (D 6) (R 6) [6,40,129,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10299
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10300 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 88 273 96 102 166 294), lower := (rows 7 42 133 88 273 96 64 128 256), losses := [] }

theorem u10300 : Upper (D 6) (R 6) [6,40,129,80,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10300
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10301 : Route 9 := (fun mask => (mask,id))

def c10301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10301 : Upper (D 6) (R 6) [6,40,129,80,258,1] 13 := by
  apply FastRouting.sound _ _ [6,40,129,80,258,1] 13 (by decide) (choices 1) [4,32] r10301 c10301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1217
  · exact u1218

def r10302 : Route 9 := (fun mask => (mask,id))

def c10302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10302 : Upper (D 6) (R 6) [6,40,129,80,258,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,80,258,4] 13 (by decide) (choices 1) [1,32] r10302 c10302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1219
  · exact u1220

def b10303 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 88 274 96 101 165 293), lower := (rows 7 42 133 88 274 96 64 128 256), losses := [] }

theorem u10303 : Upper (D 6) (R 6) [6,40,129,80,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10303
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10304 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 133 88 276 33 98 226 354), lower := (rows 7 42 133 88 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 41 17 32 98 162 290), good := (rows 478 490 156 88 276 506 64 128 256) }] }

theorem u10304 : Upper (D 6) (R 6) [6,40,129,80,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10304
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10305 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 88 276 34 97 225 353), lower := (rows 7 42 133 88 276 34 64 128 256), losses := [] }

theorem u10305 : Upper (D 6) (R 6) [6,40,129,80,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10305
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10306 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 88 276 96 99 163 291), lower := (rows 7 42 133 88 276 96 64 128 256), losses := [] }

theorem u10306 : Upper (D 6) (R 6) [6,40,129,80,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10306
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10307 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 133 88 304 33 70 198 326), lower := (rows 7 42 133 88 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 50 4 40 48 32 65 129 257), good := (rows 454 58 452 90 314 506 64 128 256) }] }

theorem u10307 : Upper (D 6) (R 6) [6,40,129,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10307
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10308 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 88 304 34 69 197 325), lower := (rows 7 42 133 88 304 34 64 128 256), losses := [] }

theorem u10308 : Upper (D 6) (R 6) [6,40,129,80,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10308
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10309 : Route 9 := (fun mask => (mask,id))

def c10309 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10309 : Upper (D 6) (R 6) [6,40,129,80,288,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,80,288,4] 13 (by decide) (choices 1) [1,2] r10309 c10309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1221
  · exact u1222

def b10310 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 133 88 304 96 71 135 263), lower := (rows 7 42 133 88 304 96 64 128 256), losses := [] }

theorem u10310 : Upper (D 6) (R 6) [6,40,129,80,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10310
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10311 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 265 52 34 80 208 336), lower := (rows 7 42 133 265 52 34 64 128 256), losses := [] }

theorem u10311 : Upper (D 6) (R 6) [6,40,129,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10311
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10312 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 133 265 52 48 66 194 322), lower := (rows 7 42 133 265 52 48 64 128 256), losses := [] }

theorem u10312 : Upper (D 6) (R 6) [6,40,129,257,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10312
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10313 : Route 9 := (fun mask => (mask,id))

def c10313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10313 : Upper (D 6) (R 6) [6,40,129,257,36,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,257,36,64] 13 (by decide) (choices 1) [2,16] r10313 c10313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1223
  · exact u1224

def b10314 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 7 42 133 265 82 36 112 240 368), lower := (rows 7 42 133 265 82 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 27 37 79 143 271), good := (rows 502 506 500 506 466 484 64 128 256) }] }

theorem u10314 : Upper (D 6) (R 6) [6,40,129,257,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10314
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10315 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 112, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 133 265 82 48 100 228 356), lower := (rows 7 42 133 265 82 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 25 63 69 133 261), good := (rows 502 58 500 506 114 48 64 128 256) }] }

theorem u10315 : Upper (D 6) (R 6) [6,40,129,257,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10315
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10316 : Route 9 := (fun mask => (mask,id))

def c10316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10316 : Upper (D 6) (R 6) [6,40,129,257,66,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,257,66,64] 13 (by decide) (choices 1) [4,16,32] r10316 c10316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1225
  · exact u1226
  · exact u1227

def b10317 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 265 84 34 112 240 368), lower := (rows 7 42 133 265 84 34 64 128 256), losses := [] }

theorem u10317 : Upper (D 6) (R 6) [6,40,129,257,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10317
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10318 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 112, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 133 265 84 48 98 226 354), lower := (rows 7 42 133 265 84 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 21 61 75 139 267), good := (rows 502 490 500 506 116 48 64 128 256) }] }

theorem u10318 : Upper (D 6) (R 6) [6,40,129,257,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10318
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10319 : Route 9 := (fun mask => (mask,id))

def c10319 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10319 : Upper (D 6) (R 6) [6,40,129,257,68,64] 13 := by
  apply FastRouting.sound _ _ [6,40,129,257,68,64] 13 (by decide) (choices 1) [2,16,32] r10319 c10319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1228
  · exact u1229
  · exact u1230

#print axioms u10319
end Delivery.IrregularNine14.P06
