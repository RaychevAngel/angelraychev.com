import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0024
import IrregularNine14P05C0025

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4260 : PairBound 9 := { available := 14, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 140 296 21 33 78 142 270), lower := (rows 19 98 140 296 21 33 64 128 256), losses := [] }

theorem u4260 : Upper (D 5) (R 5) [18,96,136,288,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4260
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4261 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 140 296 21 34 77 141 269), lower := (rows 19 98 140 296 21 34 64 128 256), losses := [] }

theorem u4261 : Upper (D 5) (R 5) [18,96,136,288,5,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4261
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4262 : Route 9 := (fun mask => (mask,id))

def c4262 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4262 : Upper (D 5) (R 5) [18,96,136,288,5,4] 13 := by
  apply FastRouting.sound _ _ [18,96,136,288,5,4] 13 (by decide) (choices 1) [1,2,8] r4262 c4262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1497
  · exact u1498
  · exact u1499

def b4263 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 98 140 296 21 40 71 135 263), lower := (rows 19 98 140 296 21 40 64 128 256), losses := [] }

theorem u4263 : Upper (D 5) (R 5) [18,96,136,288,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4263
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4264 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 98 140 296 25 33 70 134 262), lower := (rows 19 98 140 296 25 33 64 128 256), losses := [] }

theorem u4264 : Upper (D 5) (R 5) [18,96,136,288,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4264
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4265 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 19 98 140 296 25 34 69 133 261), lower := (rows 19 98 140 296 25 34 64 128 256), losses := [] }

theorem u4265 : Upper (D 5) (R 5) [18,96,136,288,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4265
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4266 : Route 9 := (fun mask => (mask,id))

def c4266 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4266 : Upper (D 5) (R 5) [18,96,136,288,9,4] 13 := by
  apply FastRouting.sound _ _ [18,96,136,288,9,4] 13 (by decide) (choices 1) [1,2,4] r4266 c4266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1500
  · exact u1501
  · exact u1502

def b4267 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 194 37 42 276 33 76 140 268), lower := (rows 19 194 37 42 276 33 64 128 256), losses := [] }

theorem u4267 : Upper (D 5) (R 5) [18,192,33,34,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4267
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4268 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 194 37 42 276 36 73 137 265), lower := (rows 19 194 37 42 276 36 64 128 256), losses := [] }

theorem u4268 : Upper (D 5) (R 5) [18,192,33,34,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4269 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 194 37 42 276 40 77 141 269), lower := (rows 19 194 37 42 276 40 64 128 256), losses := [] }

theorem u4269 : Upper (D 5) (R 5) [18,192,33,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4270 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 194 37 42 280 33 76 140 268), lower := (rows 19 194 37 42 280 33 64 128 256), losses := [] }

theorem u4270 : Upper (D 5) (R 5) [18,192,33,34,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4270
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4271 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 194 37 42 280 36 77 141 269), lower := (rows 19 194 37 42 280 36 64 128 256), losses := [] }

theorem u4271 : Upper (D 5) (R 5) [18,192,33,34,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4271
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4272 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 194 37 42 280 40 69 133 261), lower := (rows 19 194 37 42 280 40 64 128 256), losses := [] }

theorem u4272 : Upper (D 5) (R 5) [18,192,33,34,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4272
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4273 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 280, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 19 194 37 265 28 34 108 172 300), lower := (rows 19 194 37 265 28 34 64 128 256), losses := [] }

theorem u4273 : Upper (D 5) (R 5) [18,192,33,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4273
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4274 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 194 37 265 28 36 106 170 298), lower := (rows 19 194 37 265 28 36 64 128 256), losses := [] }

theorem u4274 : Upper (D 5) (R 5) [18,192,33,257,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4274
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4275 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 194, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 194 37 265 28 40 102 166 294), lower := (rows 19 194 37 265 28 40 64 128 256), losses := [] }

theorem u4275 : Upper (D 5) (R 5) [18,192,33,257,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4275
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4276 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 194 37 266 28 33 108 172 300), lower := (rows 19 194 37 266 28 33 64 128 256), losses := [] }

theorem u4276 : Upper (D 5) (R 5) [18,192,33,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4276
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4277 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 194 37 266 28 36 105 169 297), lower := (rows 19 194 37 266 28 36 64 128 256), losses := [] }

theorem u4277 : Upper (D 5) (R 5) [18,192,33,258,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4277
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4278 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 194, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 194 37 266 28 40 101 165 293), lower := (rows 19 194 37 266 28 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 69 133 261), good := (rows 501 192 485 296 508 40 64 128 256) }] }

theorem u4278 : Upper (D 5) (R 5) [18,192,33,258,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4278
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4279 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 36, targets := 8 }], pairs := [(2,3),(3,1)], upper := (rows 19 194 38 265 28 33 108 172 300), lower := (rows 19 194 38 265 28 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 41 80 144 272), good := (rows 505 192 36 297 508 41 64 128 256) }] }

theorem u4279 : Upper (D 5) (R 5) [18,192,34,257,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4279
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4280 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 194 38 265 28 36 105 169 297), lower := (rows 19 194 38 265 28 36 64 128 256), losses := [] }

theorem u4280 : Upper (D 5) (R 5) [18,192,34,257,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4280
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4281 : PairBound 9 := { available := 37, camps := [], pairs := [(2,0),(4,0)], upper := (rows 19 194 38 265 28 40 101 165 293), lower := (rows 19 194 38 265 28 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 24 56 64 128 256), good := (rows 54 194 38 316 60 56 64 128 256) }] }

theorem u4281 : Upper (D 5) (R 5) [18,192,34,257,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4281
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4282 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 194 38 265 56 33 76 140 268), lower := (rows 19 194 38 265 56 33 64 128 256), losses := [] }

theorem u4282 : Upper (D 5) (R 5) [18,192,34,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4282
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4283 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 194 38 265 56 36 77 141 269), lower := (rows 19 194 38 265 56 36 64 128 256), losses := [] }

theorem u4283 : Upper (D 5) (R 5) [18,192,34,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4283
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4284 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 38 265 56 40 69 133 261), lower := (rows 19 194 38 265 56 40 64 128 256), losses := [] }

theorem u4284 : Upper (D 5) (R 5) [18,192,34,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4284
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4285 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 194 38 268 25 33 108 172 300), lower := (rows 19 194 38 268 25 33 64 128 256), losses := [] }

theorem u4285 : Upper (D 5) (R 5) [18,192,34,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4285
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4286 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 194 38 268 25 36 105 169 297), lower := (rows 19 194 38 268 25 36 64 128 256), losses := [] }

theorem u4286 : Upper (D 5) (R 5) [18,192,34,260,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4286
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4287 : Route 9 := (fun mask => (mask,id))

def c4287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4287 : Upper (D 5) (R 5) [18,192,34,260,9,8] 13 := by
  apply FastRouting.sound _ _ [18,192,34,260,9,8] 13 (by decide) (choices 1) [1,4,32] r4287 c4287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1503
  · exact u1504
  · exact u1505

def r4288 : Route 9 := (fun mask => (mask,id))

def c4288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4288 : Upper (D 5) (R 5) [18,192,34,260,40,1] 13 := by
  apply FastRouting.sound _ _ [18,192,34,260,40,1] 13 (by decide) (choices 1) [1,4,8] r4288 c4288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1506
  · exact u1507
  · exact u1508

def b4289 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 195, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 194 38 268 56 36 73 137 265), lower := (rows 19 194 38 268 56 36 64 128 256), losses := [] }

theorem u4289 : Upper (D 5) (R 5) [18,192,34,260,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4289
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4290 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 194 38 268 56 40 69 133 261), lower := (rows 19 194 38 268 56 40 64 128 256), losses := [] }

theorem u4290 : Upper (D 5) (R 5) [18,192,34,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4290
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4291 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 194 38 296 25 33 76 140 268), lower := (rows 19 194 38 296 25 33 64 128 256), losses := [] }

theorem u4291 : Upper (D 5) (R 5) [18,192,34,288,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4291
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4292 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 194 38 296 25 36 77 141 269), lower := (rows 19 194 38 296 25 36 64 128 256), losses := [] }

theorem u4292 : Upper (D 5) (R 5) [18,192,34,288,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4292
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4293 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 194 38 296 25 40 69 133 261), lower := (rows 19 194 38 296 25 40 64 128 256), losses := [] }

theorem u4293 : Upper (D 5) (R 5) [18,192,34,288,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4293
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4294 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 194 44 266 21 33 108 172 300), lower := (rows 19 194 44 266 21 33 64 128 256), losses := [] }

theorem u4294 : Upper (D 5) (R 5) [18,192,40,258,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4294
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4295 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 194 44 266 21 36 105 169 297), lower := (rows 19 194 44 266 21 36 64 128 256), losses := [] }

theorem u4295 : Upper (D 5) (R 5) [18,192,40,258,5,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4295
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4296 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 211, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 194 44 266 21 40 101 165 293), lower := (rows 19 194 44 266 21 40 64 128 256), losses := [] }

theorem u4296 : Upper (D 5) (R 5) [18,192,40,258,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4296
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4297 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 266 49 33 76 140 268), lower := (rows 19 194 44 266 49 33 64 128 256), losses := [] }

theorem u4297 : Upper (D 5) (R 5) [18,192,40,258,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4297
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4298 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 194 44 266 49 36 77 141 269), lower := (rows 19 194 44 266 49 36 64 128 256), losses := [] }

theorem u4298 : Upper (D 5) (R 5) [18,192,40,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4298
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4299 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 211, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 194 44 266 49 40 69 133 261), lower := (rows 19 194 44 266 49 40 64 128 256), losses := [] }

theorem u4299 : Upper (D 5) (R 5) [18,192,40,258,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4299
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4300 : PairBound 9 := { available := 42, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 194 44 268 21 33 106 170 298), lower := (rows 19 194 44 268 21 33 64 128 256), losses := [] }

theorem u4300 : Upper (D 5) (R 5) [18,192,40,260,5,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4300
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4301 : Route 9 := (fun mask => (mask,id))

def c4301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4301 : Upper (D 5) (R 5) [18,192,40,260,5,2] 13 := by
  apply FastRouting.sound _ _ [18,192,40,260,5,2] 13 (by decide) (choices 1) [1,8,32] r4301 c4301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1509
  · exact u1510
  · exact u1511

def b4302 : PairBound 9 := { available := 35, camps := [{ cop := 8, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 194 44 268 21 40 99 163 291), lower := (rows 19 194 44 268 21 40 64 128 256), losses := [] }

theorem u4302 : Upper (D 5) (R 5) [18,192,40,260,5,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4302
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4303 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 194 44 268 25 33 102 166 294), lower := (rows 19 194 44 268 25 33 64 128 256), losses := [] }

theorem u4303 : Upper (D 5) (R 5) [18,192,40,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4303
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4304 : Route 9 := (fun mask => (mask,id))

def c4304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4304 : Upper (D 5) (R 5) [18,192,40,260,9,2] 13 := by
  apply FastRouting.sound _ _ [18,192,40,260,9,2] 13 (by decide) (choices 1) [1,4,32] r4304 c4304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1512
  · exact u1513
  · exact u1514

def b4305 : PairBound 9 := { available := 35, camps := [{ cop := 8, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 194 44 268 25 36 99 163 291), lower := (rows 19 194 44 268 25 36 64 128 256), losses := [] }

theorem u4305 : Upper (D 5) (R 5) [18,192,40,260,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4305
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4306 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 268 49 33 78 142 270), lower := (rows 19 194 44 268 49 33 64 128 256), losses := [] }

theorem u4306 : Upper (D 5) (R 5) [18,192,40,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4306
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4307 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 194 44 268 49 34 77 141 269), lower := (rows 19 194 44 268 49 34 64 128 256), losses := [] }

theorem u4307 : Upper (D 5) (R 5) [18,192,40,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4307
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4308 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 194 44 268 49 36 75 139 267), lower := (rows 19 194 44 268 49 36 64 128 256), losses := [] }

theorem u4308 : Upper (D 5) (R 5) [18,192,40,260,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4308
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4309 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 194 44 268 49 40 71 135 263), lower := (rows 19 194 44 268 49 40 64 128 256), losses := [] }

theorem u4309 : Upper (D 5) (R 5) [18,192,40,260,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4309
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4310 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 137 22 36 344 408 280), lower := (rows 35 67 44 137 22 36 64 128 256), losses := [] }

theorem u4310 : Upper (D 5) (R 5) [34,65,40,129,6,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4310
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4311 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 137 22 40 340 404 276), lower := (rows 35 67 44 137 22 40 64 128 256), losses := [] }

theorem u4311 : Upper (D 5) (R 5) [34,65,40,129,6,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4311
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4312 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 44 137 22 48 332 396 268), lower := (rows 35 67 44 137 22 48 64 128 256), losses := [] }

theorem u4312 : Upper (D 5) (R 5) [34,65,40,129,6,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4312
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4313 : Route 9 := (fun mask => (mask,id))

def c4313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4313 : Upper (D 5) (R 5) [34,65,40,129,6,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,6,256] 13 (by decide) (choices 1) [4,8,16] r4313 c4313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1515
  · exact u1516
  · exact u1517

def b4314 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 137 274 36 92 156 284), lower := (rows 35 67 44 137 274 36 64 128 256), losses := [] }

theorem u4314 : Upper (D 5) (R 5) [34,65,40,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4314
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4315 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 137 274 40 84 148 276), lower := (rows 35 67 44 137 274 40 64 128 256), losses := [] }

theorem u4315 : Upper (D 5) (R 5) [34,65,40,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4315
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4316 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 44 137 274 48 76 140 268), lower := (rows 35 67 44 137 274 48 64 128 256), losses := [] }

theorem u4316 : Upper (D 5) (R 5) [34,65,40,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4316
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4317 : PairBound 9 := { available := 28, camps := [{ cop := 6, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 67 44 137 276 34 92 156 284), lower := (rows 35 67 44 137 276 34 64 128 256), losses := [] }

theorem u4317 : Upper (D 5) (R 5) [34,65,40,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4317
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4318 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 137 276 36 90 154 282), lower := (rows 35 67 44 137 276 36 64 128 256), losses := [] }

theorem u4318 : Upper (D 5) (R 5) [34,65,40,129,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4318
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4319 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 67 44 137 276 40 86 150 278), lower := (rows 35 67 44 137 276 40 64 128 256), losses := [] }

theorem u4319 : Upper (D 5) (R 5) [34,65,40,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4319
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4319
end Delivery.IrregularNine14.P05
