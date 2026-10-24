import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0020

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4440 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 38 138 80 173 205 141 397), lower := (rows 113 274 38 138 80 32 64 128 256), losses := [] }

theorem u4440 : Upper (D 1) (R 1) [112,272,34,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4440
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4441 : Route 9 := (fun mask => (mask,id))

def c4441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4441 : Upper (D 1) (R 1) [112,272,34,130,128] 13 := by
  apply FastRouting.sound _ _ [112,272,34,130,128] 13 (by decide) (choices 1) [1,4,8,64] r4441 c4441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1231
  · exact u1232
  · exact u1233
  · exact u1234

def b4442 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 274 38 140 17 234 202 202 458), lower := (rows 113 274 38 140 17 32 64 128 256), losses := [] }

theorem u4442 : Upper (D 1) (R 1) [112,272,34,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4442
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4443 : PairBound 9 := { available := 201, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 38 140 18 233 201 201 457), lower := (rows 113 274 38 140 18 32 64 128 256), losses := [] }

theorem u4443 : Upper (D 1) (R 1) [112,272,34,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4443
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4444 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 274 38 140 24 227 195 195 451), lower := (rows 113 274 38 140 24 32 64 128 256), losses := [] }

theorem u4444 : Upper (D 1) (R 1) [112,272,34,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4444
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4445 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 38 140 80 171 203 139 395), lower := (rows 113 274 38 140 80 32 64 128 256), losses := [] }

theorem u4445 : Upper (D 1) (R 1) [112,272,34,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4446 : Route 9 := (fun mask => (mask,id))

def c4446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4446 : Upper (D 1) (R 1) [112,272,34,132,128] 13 := by
  apply FastRouting.sound _ _ [112,272,34,132,128] 13 (by decide) (choices 1) [1,2,8,64] r4446 c4446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1235
  · exact u1236
  · exact u1237
  · exact u1238

def b4447 : PairBound 9 := { available := 142, camps := [], pairs := [], upper := (rows 113 274 38 200 17 174 206 142 398), lower := (rows 113 274 38 200 17 32 64 128 256), losses := [] }

theorem u4447 : Upper (D 1) (R 1) [112,272,34,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4447
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4448 : PairBound 9 := { available := 141, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 38 200 18 173 205 141 397), lower := (rows 113 274 38 200 18 32 64 128 256), losses := [] }

theorem u4448 : Upper (D 1) (R 1) [112,272,34,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4448
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4449 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 113 274 38 200 20 171 203 139 395), lower := (rows 113 274 38 200 20 32 64 128 256), losses := [] }

theorem u4449 : Upper (D 1) (R 1) [112,272,34,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4449
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4450 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 113 274 38 200 24 167 199 135 391), lower := (rows 113 274 38 200 24 32 64 128 256), losses := [] }

theorem u4450 : Upper (D 1) (R 1) [112,272,34,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4450
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4451 : Route 9 := (fun mask => (mask,id))

def c4451 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4451 : Upper (D 1) (R 1) [112,272,34,192,128] 13 := by
  apply FastRouting.sound _ _ [112,272,34,192,128] 13 (by decide) (choices 1) [1,2,4,8] r4451 c4451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1239
  · exact u1240
  · exact u1241
  · exact u1242

def b4452 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 113 274 44 138 17 230 198 198 454), lower := (rows 113 274 44 138 17 32 64 128 256), losses := [] }

theorem u4452 : Upper (D 1) (R 1) [112,272,40,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4452
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4453 : PairBound 9 := { available := 197, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 44 138 18 229 197 197 453), lower := (rows 113 274 44 138 18 32 64 128 256), losses := [] }

theorem u4453 : Upper (D 1) (R 1) [112,272,40,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4453
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4454 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 274 44 138 20 227 195 195 451), lower := (rows 113 274 44 138 20 32 64 128 256), losses := [] }

theorem u4454 : Upper (D 1) (R 1) [112,272,40,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4454
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4455 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 44 138 80 167 199 135 391), lower := (rows 113 274 44 138 80 32 64 128 256), losses := [] }

theorem u4455 : Upper (D 1) (R 1) [112,272,40,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4455
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4456 : Route 9 := (fun mask => (mask,id))

def c4456 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4456 : Upper (D 1) (R 1) [112,272,40,130,128] 13 := by
  apply FastRouting.sound _ _ [112,272,40,130,128] 13 (by decide) (choices 1) [1,2,4,64] r4456 c4456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1243
  · exact u1244
  · exact u1245
  · exact u1246

def b4457 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 113 274 44 200 17 166 198 134 390), lower := (rows 113 274 44 200 17 32 64 128 256), losses := [] }

theorem u4457 : Upper (D 1) (R 1) [112,272,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4457
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4458 : PairBound 9 := { available := 135, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 44 200 18 167 199 135 391), lower := (rows 113 274 44 200 18 32 64 128 256), losses := [] }

theorem u4458 : Upper (D 1) (R 1) [112,272,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4458
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4459 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 274 44 200 20 163 195 131 387), lower := (rows 113 274 44 200 20 32 64 128 256), losses := [] }

theorem u4459 : Upper (D 1) (R 1) [112,272,40,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4459
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4460 : Route 9 := (fun mask => (mask,id))

def c4460 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4460 : Upper (D 1) (R 1) [112,272,40,192,128] 13 := by
  apply FastRouting.sound _ _ [112,272,40,192,128] 13 (by decide) (choices 1) [1,2,4] r4460 c4460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1247
  · exact u1248
  · exact u1249

def b4461 : PairBound 9 := { available := 108, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 133 138 18 108 108 236 364), lower := (rows 113 274 133 138 18 32 64 128 256), losses := [] }

theorem u4461 : Upper (D 1) (R 1) [112,272,129,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4461
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4462 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 274 133 138 20 106 106 234 362), lower := (rows 113 274 133 138 20 32 64 128 256), losses := [] }

theorem u4462 : Upper (D 1) (R 1) [112,272,129,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4462
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4463 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 113 274 133 138 24 102 102 230 358), lower := (rows 113 274 133 138 24 32 64 128 256), losses := [] }

theorem u4463 : Upper (D 1) (R 1) [112,272,129,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4463
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4464 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 133 138 48 110 78 206 334), lower := (rows 113 274 133 138 48 32 64 128 256), losses := [] }

theorem u4464 : Upper (D 1) (R 1) [112,272,129,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4464
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4465 : PairBound 9 := { available := 78, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 133 168 18 110 78 206 334), lower := (rows 113 274 133 168 18 32 64 128 256), losses := [] }

theorem u4465 : Upper (D 1) (R 1) [112,272,129,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4465
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4466 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 274 133 168 20 106 74 202 330), lower := (rows 113 274 133 168 20 32 64 128 256), losses := [] }

theorem u4466 : Upper (D 1) (R 1) [112,272,129,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4466
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4467 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 274 133 168 24 102 70 198 326), lower := (rows 113 274 133 168 24 32 64 128 256), losses := [] }

theorem u4467 : Upper (D 1) (R 1) [112,272,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4467
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4468 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 133 168 80 46 78 142 270), lower := (rows 113 274 133 168 80 32 64 128 256), losses := [] }

theorem u4468 : Upper (D 1) (R 1) [112,272,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4468
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4469 : PairBound 9 := { available := 78, camps := [], pairs := [], upper := (rows 113 274 134 168 17 110 78 206 334), lower := (rows 113 274 134 168 17 32 64 128 256), losses := [] }

theorem u4469 : Upper (D 1) (R 1) [112,272,130,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4470 : PairBound 9 := { available := 77, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 134 168 18 109 77 205 333), lower := (rows 113 274 134 168 18 32 64 128 256), losses := [] }

theorem u4470 : Upper (D 1) (R 1) [112,272,130,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4470
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4471 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 274 134 168 20 107 75 203 331), lower := (rows 113 274 134 168 20 32 64 128 256), losses := [] }

theorem u4471 : Upper (D 1) (R 1) [112,272,130,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4471
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4472 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 113 274 134 168 24 103 71 199 327), lower := (rows 113 274 134 168 24 32 64 128 256), losses := [] }

theorem u4472 : Upper (D 1) (R 1) [112,272,130,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4472
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4473 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 134 168 80 47 79 143 271), lower := (rows 113 274 134 168 80 32 64 128 256), losses := [] }

theorem u4473 : Upper (D 1) (R 1) [112,272,130,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4473
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4474 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 113 274 164 200 17 46 78 142 270), lower := (rows 113 274 164 200 17 32 64 128 256), losses := [] }

theorem u4474 : Upper (D 1) (R 1) [112,272,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4474
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4475 : PairBound 9 := { available := 15, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 164 200 18 47 79 143 271), lower := (rows 113 274 164 200 18 32 64 128 256), losses := [] }

theorem u4475 : Upper (D 1) (R 1) [112,272,160,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4475
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4476 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 113 274 164 200 20 43 75 139 267), lower := (rows 113 274 164 200 20 32 64 128 256), losses := [] }

theorem u4476 : Upper (D 1) (R 1) [112,272,160,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4476
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4477 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 113 386 7 26 20 232 232 232 488), lower := (rows 113 386 7 26 20 32 64 128 256), losses := [] }

theorem u4477 : Upper (D 1) (R 1) [112,384,3,18,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4477
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4478 : PairBound 9 := { available := 228, camps := [], pairs := [], upper := (rows 113 386 7 26 24 228 228 228 484), lower := (rows 113 386 7 26 24 32 64 128 256), losses := [] }

theorem u4478 : Upper (D 1) (R 1) [112,384,3,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4478
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4479 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 386 7 26 48 236 204 204 460), lower := (rows 113 386 7 26 48 32 64 128 256), losses := [] }

theorem u4479 : Upper (D 1) (R 1) [112,384,3,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4479
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4480 : PairBound 9 := { available := 108, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 386 7 26 144 108 108 236 364), lower := (rows 113 386 7 26 144 32 64 128 256), losses := [] }

theorem u4480 : Upper (D 1) (R 1) [112,384,3,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4480
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4481 : PairBound 9 := { available := 120, camps := [], pairs := [(0,7)], upper := (rows 113 386 7 140 18 120 120 248 376), lower := (rows 113 386 7 140 18 32 64 128 256), losses := [{ target := 7, region := (rows 9 2 4 8 22 40 72 0 264), good := (rows 113 274 23 381 18 32 64 0 256) }] }

theorem u4481 : Upper (D 1) (R 1) [112,384,3,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4481
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4482 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 113 386 7 140 24 114 114 242 370), lower := (rows 113 386 7 140 24 32 64 128 256), losses := [] }

theorem u4482 : Upper (D 1) (R 1) [112,384,3,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4482
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4483 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 386 7 140 48 122 90 218 346), lower := (rows 113 386 7 140 48 32 64 128 256), losses := [] }

theorem u4483 : Upper (D 1) (R 1) [112,384,3,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4483
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4484 : PairBound 9 := { available := 108, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 386 7 152 18 108 108 236 364), lower := (rows 113 386 7 152 18 32 64 128 256), losses := [] }

theorem u4484 : Upper (D 1) (R 1) [112,384,3,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4484
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4485 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 386 7 152 20 106 106 234 362), lower := (rows 113 386 7 152 20 32 64 128 256), losses := [] }

theorem u4485 : Upper (D 1) (R 1) [112,384,3,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4485
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4486 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 113 386 7 152 24 102 102 230 358), lower := (rows 113 386 7 152 24 32 64 128 256), losses := [] }

theorem u4486 : Upper (D 1) (R 1) [112,384,3,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4486
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4487 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 386 7 152 48 110 78 206 334), lower := (rows 113 386 7 152 48 32 64 128 256), losses := [] }

theorem u4487 : Upper (D 1) (R 1) [112,384,3,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4487
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4488 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 386 13 14 18 240 240 240 496), lower := (rows 113 386 13 14 18 32 64 128 256), losses := [] }

theorem u4488 : Upper (D 1) (R 1) [112,384,9,6,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4488
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4489 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 386 13 14 48 242 210 210 466), lower := (rows 113 386 13 14 48 32 64 128 256), losses := [] }

theorem u4489 : Upper (D 1) (R 1) [112,384,9,6,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4489
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4490_2 : Upper (D 1) (R 1) [112,384,9,6,128,2] 13 :=
  permutation_upper _ _ _ [112,384,9,6,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1250

theorem m4490_16 : Upper (D 1) (R 1) [112,384,9,6,128,16] 13 :=
  permutation_upper _ _ _ [112,384,9,6,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1251

theorem m4490_64 : Upper (D 1) (R 1) [112,384,9,6,128,64] 13 :=
  permutation_upper _ _ _ [112,384,9,6,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1252

def r4490 : Route 9 := (fun mask => (mask,id))

def c4490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4490 : Upper (D 1) (R 1) [112,384,9,6,128] 13 := by
  apply FastRouting.sound _ _ [112,384,9,6,128] 13 (by decide) (choices 1) [2,16,64] r4490 c4490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4490_2
  · exact m4490_16
  · exact m4490_64

def b4491 : PairBound 9 := { available := 204, camps := [], pairs := [], upper := (rows 113 386 22 42 17 236 204 204 460), lower := (rows 113 386 22 42 17 32 64 128 256), losses := [] }

theorem u4491 : Upper (D 1) (R 1) [112,384,18,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4491
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4492 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 113 386 22 42 20 233 201 201 457), lower := (rows 113 386 22 42 20 32 64 128 256), losses := [] }

theorem u4492 : Upper (D 1) (R 1) [112,384,18,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4492
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4493 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 113 386 22 42 24 229 197 197 453), lower := (rows 113 386 22 42 24 32 64 128 256), losses := [] }

theorem u4493 : Upper (D 1) (R 1) [112,384,18,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4493
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4494 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 386 22 42 80 173 205 141 397), lower := (rows 113 386 22 42 80 32 64 128 256), losses := [] }

theorem u4494 : Upper (D 1) (R 1) [112,384,18,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4494
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4495 : PairBound 9 := { available := 77, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 386 22 42 144 109 77 205 333), lower := (rows 113 386 22 42 144 32 64 128 256), losses := [] }

theorem u4495 : Upper (D 1) (R 1) [112,384,18,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4495
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4496 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 386 22 44 17 234 202 202 458), lower := (rows 113 386 22 44 17 32 64 128 256), losses := [] }

theorem u4496 : Upper (D 1) (R 1) [112,384,18,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4496
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4497 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 386 22 44 18 233 201 201 457), lower := (rows 113 386 22 44 18 32 64 128 256), losses := [] }

theorem u4497 : Upper (D 1) (R 1) [112,384,18,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4497
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4498 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 386 22 44 24 227 195 195 451), lower := (rows 113 386 22 44 24 32 64 128 256), losses := [] }

theorem u4498 : Upper (D 1) (R 1) [112,384,18,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4498
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4499 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 386 22 44 80 171 203 139 395), lower := (rows 113 386 22 44 80 32 64 128 256), losses := [] }

theorem u4499 : Upper (D 1) (R 1) [112,384,18,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4499
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4499
end Delivery.IrregularNine14.P01
