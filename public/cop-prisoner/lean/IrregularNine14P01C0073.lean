import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0019
import IrregularNine14P01C0020

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4380 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 140 11 48 242 210 210 466), lower := (rows 113 262 140 11 48 32 64 128 256), losses := [] }

theorem u4380 : Upper (D 1) (R 1) [112,260,136,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4380
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4381_2 : Upper (D 1) (R 1) [112,260,136,3,128,2] 13 :=
  permutation_upper _ _ _ [112,260,136,3,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1189

theorem m4381_16 : Upper (D 1) (R 1) [112,260,136,3,128,16] 13 :=
  permutation_upper _ _ _ [112,260,136,3,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1190

theorem m4381_64 : Upper (D 1) (R 1) [112,260,136,3,128,64] 13 :=
  permutation_upper _ _ _ [112,260,136,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1191

def r4381 : Route 9 := (fun mask => (mask,id))

def c4381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4381 : Upper (D 1) (R 1) [112,260,136,3,128] 13 := by
  apply FastRouting.sound _ _ [112,260,136,3,128] 13 (by decide) (choices 1) [2,16,64] r4381 c4381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4381_2
  · exact m4381_16
  · exact m4381_64

def b4382 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 262 140 26 17 226 226 226 482), lower := (rows 113 262 140 26 17 32 64 128 256), losses := [] }

theorem u4382 : Upper (D 1) (R 1) [112,260,136,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4382
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4383 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 262 140 26 18 225 225 225 481), lower := (rows 113 262 140 26 18 32 64 128 256), losses := [] }

theorem u4383 : Upper (D 1) (R 1) [112,260,136,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4383
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4384 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 140 26 48 227 195 195 451), lower := (rows 113 262 140 26 48 32 64 128 256), losses := [] }

theorem u4384 : Upper (D 1) (R 1) [112,260,136,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4384
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4385 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 140 26 144 99 99 227 355), lower := (rows 113 262 140 26 144 32 64 128 256), losses := [] }

theorem u4385 : Upper (D 1) (R 1) [112,260,136,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4385
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4386 : Route 9 := (fun mask => (mask,id))

def c4386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4386 : Upper (D 1) (R 1) [112,260,144,3,2] 13 := by
  apply FastRouting.sound _ _ [112,260,144,3,2] 13 (by decide) (choices 1) [8,64,128] r4386 c4386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1192
  · exact u1193
  · exact u1194

def b4387 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 262 148 11 24 226 226 226 482), lower := (rows 113 262 148 11 24 32 64 128 256), losses := [] }

theorem u4387 : Upper (D 1) (R 1) [112,260,144,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4387
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4388 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 148 11 48 234 202 202 458), lower := (rows 113 262 148 11 48 32 64 128 256), losses := [] }

theorem u4388 : Upper (D 1) (R 1) [112,260,144,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4388
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4389 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 148 11 144 106 106 234 362), lower := (rows 113 262 148 11 144 32 64 128 256), losses := [] }

theorem u4389 : Upper (D 1) (R 1) [112,260,144,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4389
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4390 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 262 148 42 17 234 202 202 458), lower := (rows 113 262 148 42 17 32 64 128 256), losses := [] }

theorem u4390 : Upper (D 1) (R 1) [112,260,144,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4390
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4391 : Route 9 := (fun mask => (mask,id))

def c4391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4391 : Upper (D 1) (R 1) [112,260,144,34,2] 13 := by
  apply FastRouting.sound _ _ [112,260,144,34,2] 13 (by decide) (choices 1) [1,8,64,128] r4391 c4391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1195
  · exact u1196
  · exact u1197
  · exact u1198

def b4392 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 262 148 42 24 227 195 195 451), lower := (rows 113 262 148 42 24 32 64 128 256), losses := [] }

theorem u4392 : Upper (D 1) (R 1) [112,260,144,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4392
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4393 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 148 42 80 171 203 139 395), lower := (rows 113 262 148 42 80 32 64 128 256), losses := [] }

theorem u4393 : Upper (D 1) (R 1) [112,260,144,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4393
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4394 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 148 42 144 107 75 203 331), lower := (rows 113 262 148 42 144 32 64 128 256), losses := [] }

theorem u4394 : Upper (D 1) (R 1) [112,260,144,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4394
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4395 : Route 9 := (fun mask => (mask,id))

def c4395 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4395 : Upper (D 1) (R 1) [112,260,144,129,2] 13 := by
  apply FastRouting.sound _ _ [112,260,144,129,2] 13 (by decide) (choices 1) [2,8,64] r4395 c4395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1199
  · exact u1200
  · exact u1201

def b4396 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 262 148 137 24 98 98 226 354), lower := (rows 113 262 148 137 24 32 64 128 256), losses := [] }

theorem u4396 : Upper (D 1) (R 1) [112,260,144,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4396
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4397 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 148 137 48 106 74 202 330), lower := (rows 113 262 148 137 48 32 64 128 256), losses := [] }

theorem u4397 : Upper (D 1) (R 1) [112,260,144,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4397
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4398 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 262 148 168 17 106 74 202 330), lower := (rows 113 262 148 168 17 32 64 128 256), losses := [] }

theorem u4398 : Upper (D 1) (R 1) [112,260,144,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4398
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4399 : Route 9 := (fun mask => (mask,id))

def c4399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4399 : Upper (D 1) (R 1) [112,260,144,160,2] 13 := by
  apply FastRouting.sound _ _ [112,260,144,160,2] 13 (by decide) (choices 1) [1,2,8,64] r4399 c4399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1202
  · exact u1203
  · exact u1204
  · exact u1205

def b4400 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 262 148 168 24 99 67 195 323), lower := (rows 113 262 148 168 24 32 64 128 256), losses := [] }

theorem u4400 : Upper (D 1) (R 1) [112,260,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4400
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4401 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 148 168 80 43 75 139 267), lower := (rows 113 262 148 168 80 32 64 128 256), losses := [] }

theorem u4401 : Upper (D 1) (R 1) [112,260,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4401
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4402 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 13 14 18 224 224 224 480), lower := (rows 113 274 13 14 18 32 64 128 256), losses := [] }

theorem u4402 : Upper (D 1) (R 1) [112,272,9,6,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4402
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4403 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 13 14 48 226 194 194 450), lower := (rows 113 274 13 14 48 32 64 128 256), losses := [] }

theorem u4403 : Upper (D 1) (R 1) [112,272,9,6,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4403
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4404 : Route 9 := (fun mask => (mask,id))

def c4404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4404 : Upper (D 1) (R 1) [112,272,9,6,128] 13 := by
  apply FastRouting.sound _ _ [112,272,9,6,128] 13 (by decide) (choices 1) [2,64,128] r4404 c4404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1206
  · exact u1207
  · exact u1208

def b4405 : PairBound 9 := { available := 228, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 13 138 18 228 228 228 484), lower := (rows 113 274 13 138 18 32 64 128 256), losses := [] }

theorem u4405 : Upper (D 1) (R 1) [112,272,9,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4405
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4406 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 274 13 138 20 226 226 226 482), lower := (rows 113 274 13 138 20 32 64 128 256), losses := [] }

theorem u4406 : Upper (D 1) (R 1) [112,272,9,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4406
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4407 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 13 138 48 230 198 198 454), lower := (rows 113 274 13 138 48 32 64 128 256), losses := [] }

theorem u4407 : Upper (D 1) (R 1) [112,272,9,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4407
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4408 : Route 9 := (fun mask => (mask,id))

def c4408 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4408 : Upper (D 1) (R 1) [112,272,9,130,128] 13 := by
  apply FastRouting.sound _ _ [112,272,9,130,128] 13 (by decide) (choices 1) [2,4,64] r4408 c4408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1209
  · exact u1210
  · exact u1211

def b4409 : PairBound 9 := { available := 226, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 13 140 18 226 226 226 482), lower := (rows 113 274 13 140 18 32 64 128 256), losses := [] }

theorem u4409 : Upper (D 1) (R 1) [112,272,9,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4409
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4410 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 13 140 48 226 194 194 450), lower := (rows 113 274 13 140 48 32 64 128 256), losses := [] }

theorem u4410 : Upper (D 1) (R 1) [112,272,9,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4410
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4411 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 113 274 13 140 144 98 98 226 354), lower := (rows 113 274 13 140 144 32 64 128 256), losses := [] }

theorem u4411 : Upper (D 1) (R 1) [112,272,9,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4411
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4412 : PairBound 9 := { available := 228, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 14 137 18 228 228 228 484), lower := (rows 113 274 14 137 18 32 64 128 256), losses := [] }

theorem u4412 : Upper (D 1) (R 1) [112,272,10,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4412
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4413 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 274 14 137 20 226 226 226 482), lower := (rows 113 274 14 137 20 32 64 128 256), losses := [] }

theorem u4413 : Upper (D 1) (R 1) [112,272,10,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4413
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4414 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 14 137 48 230 198 198 454), lower := (rows 113 274 14 137 48 32 64 128 256), losses := [] }

theorem u4414 : Upper (D 1) (R 1) [112,272,10,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4414
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4415 : Route 9 := (fun mask => (mask,id))

def c4415 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4415 : Upper (D 1) (R 1) [112,272,10,129,128] 13 := by
  apply FastRouting.sound _ _ [112,272,10,129,128] 13 (by decide) (choices 1) [2,4,64] r4415 c4415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1212
  · exact u1213
  · exact u1214

def b4416 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 274 14 140 17 226 226 226 482), lower := (rows 113 274 14 140 17 32 64 128 256), losses := [] }

theorem u4416 : Upper (D 1) (R 1) [112,272,10,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4416
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4417 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 14 140 18 225 225 225 481), lower := (rows 113 274 14 140 18 32 64 128 256), losses := [] }

theorem u4417 : Upper (D 1) (R 1) [112,272,10,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4417
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4418 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 14 140 48 227 195 195 451), lower := (rows 113 274 14 140 48 32 64 128 256), losses := [] }

theorem u4418 : Upper (D 1) (R 1) [112,272,10,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4418
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4419 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 113 274 14 140 144 99 99 227 355), lower := (rows 113 274 14 140 144 32 64 128 256), losses := [] }

theorem u4419 : Upper (D 1) (R 1) [112,272,10,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4419
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4420 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 113 274 14 168 17 230 198 198 454), lower := (rows 113 274 14 168 17 32 64 128 256), losses := [] }

theorem u4420 : Upper (D 1) (R 1) [112,272,10,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4420
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4421 : PairBound 9 := { available := 197, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 14 168 18 229 197 197 453), lower := (rows 113 274 14 168 18 32 64 128 256), losses := [] }

theorem u4421 : Upper (D 1) (R 1) [112,272,10,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4421
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4422 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 274 14 168 20 227 195 195 451), lower := (rows 113 274 14 168 20 32 64 128 256), losses := [] }

theorem u4422 : Upper (D 1) (R 1) [112,272,10,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4422
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4423 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 14 168 80 167 199 135 391), lower := (rows 113 274 14 168 80 32 64 128 256), losses := [] }

theorem u4423 : Upper (D 1) (R 1) [112,272,10,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4423
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4424 : Route 9 := (fun mask => (mask,id))

def c4424 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4424 : Upper (D 1) (R 1) [112,272,10,160,128] 13 := by
  apply FastRouting.sound _ _ [112,272,10,160,128] 13 (by decide) (choices 1) [1,2,4,64] r4424 c4424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1215
  · exact u1216
  · exact u1217
  · exact u1218

def b4425 : PairBound 9 := { available := 140, camps := [], pairs := [], upper := (rows 113 274 38 74 17 172 204 140 396), lower := (rows 113 274 38 74 17 32 64 128 256), losses := [] }

theorem u4425 : Upper (D 1) (R 1) [112,272,34,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4425
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4426 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 113 274 38 74 20 169 201 137 393), lower := (rows 113 274 38 74 20 32 64 128 256), losses := [] }

theorem u4426 : Upper (D 1) (R 1) [112,272,34,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4426
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4427 : Route 9 := (fun mask => (mask,id))

def c4427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4427 : Upper (D 1) (R 1) [112,272,34,66,128] 13 := by
  apply FastRouting.sound _ _ [112,272,34,66,128] 13 (by decide) (choices 1) [1,4,8,128] r4427 c4427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1219
  · exact u1220
  · exact u1221
  · exact u1222

def b4428 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 113 274 38 76 17 170 202 138 394), lower := (rows 113 274 38 76 17 32 64 128 256), losses := [] }

theorem u4428 : Upper (D 1) (R 1) [112,272,34,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4428
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4429 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 38 76 18 169 201 137 393), lower := (rows 113 274 38 76 18 32 64 128 256), losses := [] }

theorem u4429 : Upper (D 1) (R 1) [112,272,34,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4429
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4430 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 274 38 76 24 163 195 131 387), lower := (rows 113 274 38 76 24 32 64 128 256), losses := [] }

theorem u4430 : Upper (D 1) (R 1) [112,272,34,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4430
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4431 : Route 9 := (fun mask => (mask,id))

def c4431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4431 : Upper (D 1) (R 1) [112,272,34,68,128] 13 := by
  apply FastRouting.sound _ _ [112,272,34,68,128] 13 (by decide) (choices 1) [1,2,8,128] r4431 c4431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1223
  · exact u1224
  · exact u1225
  · exact u1226

def b4432 : PairBound 9 := { available := 204, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 38 137 18 236 204 204 460), lower := (rows 113 274 38 137 18 32 64 128 256), losses := [] }

theorem u4432 : Upper (D 1) (R 1) [112,272,34,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4432
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4433 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 274 38 137 20 234 202 202 458), lower := (rows 113 274 38 137 20 32 64 128 256), losses := [] }

theorem u4433 : Upper (D 1) (R 1) [112,272,34,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4433
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4434 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 113 274 38 137 24 230 198 198 454), lower := (rows 113 274 38 137 24 32 64 128 256), losses := [] }

theorem u4434 : Upper (D 1) (R 1) [112,272,34,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4434
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4435 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 38 137 80 174 206 142 398), lower := (rows 113 274 38 137 80 32 64 128 256), losses := [] }

theorem u4435 : Upper (D 1) (R 1) [112,272,34,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4435
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4436 : Route 9 := (fun mask => (mask,id))

def c4436 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4436 : Upper (D 1) (R 1) [112,272,34,129,128] 13 := by
  apply FastRouting.sound _ _ [112,272,34,129,128] 13 (by decide) (choices 1) [2,4,8,64] r4436 c4436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1227
  · exact u1228
  · exact u1229
  · exact u1230

def b4437 : PairBound 9 := { available := 204, camps := [], pairs := [], upper := (rows 113 274 38 138 17 236 204 204 460), lower := (rows 113 274 38 138 17 32 64 128 256), losses := [] }

theorem u4437 : Upper (D 1) (R 1) [112,272,34,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4437
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4438 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 113 274 38 138 20 233 201 201 457), lower := (rows 113 274 38 138 20 32 64 128 256), losses := [] }

theorem u4438 : Upper (D 1) (R 1) [112,272,34,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4438
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4439 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 113 274 38 138 24 229 197 197 453), lower := (rows 113 274 38 138 24 32 64 128 256), losses := [] }

theorem u4439 : Upper (D 1) (R 1) [112,272,34,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4439
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4439
end Delivery.IrregularNine14.P01
