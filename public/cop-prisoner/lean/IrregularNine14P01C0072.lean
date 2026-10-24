import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0019

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4320 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 259 28 168 80 166 198 134 390), lower := (rows 113 259 28 168 80 32 64 128 256), losses := [] }

theorem u4320 : Upper (D 1) (R 1) [112,257,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4320
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4321 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 28 168 144 102 70 198 326), lower := (rows 113 259 28 168 144 32 64 128 256), losses := [] }

theorem u4321 : Upper (D 1) (R 1) [112,257,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4321
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4322 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 259 134 152 18 108 108 236 364), lower := (rows 113 259 134 152 18 32 64 128 256), losses := [] }

theorem u4322 : Upper (D 1) (R 1) [112,257,130,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4322
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4323 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 259 134 152 20 106 106 234 362), lower := (rows 113 259 134 152 20 32 64 128 256), losses := [] }

theorem u4323 : Upper (D 1) (R 1) [112,257,130,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4323
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4324 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 113 259 134 152 24 102 102 230 358), lower := (rows 113 259 134 152 24 32 64 128 256), losses := [] }

theorem u4324 : Upper (D 1) (R 1) [112,257,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4324
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4325 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 259 134 152 48 110 78 206 334), lower := (rows 113 259 134 152 48 32 64 128 256), losses := [] }

theorem u4325 : Upper (D 1) (R 1) [112,257,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4325
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4326 : Route 9 := (fun mask => (mask,id))

def c4326 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4326 : Upper (D 1) (R 1) [112,257,144,160,2] 13 := by
  apply FastRouting.sound _ _ [112,257,144,160,2] 13 (by decide) (choices 1) [2,4,8,64] r4326 c4326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1161
  · exact u1162
  · exact u1163
  · exact u1164

def b4327 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 259 148 168 20 106 74 202 330), lower := (rows 113 259 148 168 20 32 64 128 256), losses := [] }

theorem u4327 : Upper (D 1) (R 1) [112,257,144,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4327
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4328 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 259 148 168 24 102 70 198 326), lower := (rows 113 259 148 168 24 32 64 128 256), losses := [] }

theorem u4328 : Upper (D 1) (R 1) [112,257,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4328
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4329 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 259 148 168 80 46 78 142 270), lower := (rows 113 259 148 168 80 32 64 128 256), losses := [] }

theorem u4329 : Upper (D 1) (R 1) [112,257,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4329
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4330 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 7 152 18 232 232 232 488), lower := (rows 113 262 7 152 18 32 64 128 256), losses := [] }

theorem u4330 : Upper (D 1) (R 1) [112,260,3,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4330
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4331 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 262 7 152 24 226 226 226 482), lower := (rows 113 262 7 152 24 32 64 128 256), losses := [] }

theorem u4331 : Upper (D 1) (R 1) [112,260,3,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4332 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 7 152 48 234 202 202 458), lower := (rows 113 262 7 152 48 32 64 128 256), losses := [] }

theorem u4332 : Upper (D 1) (R 1) [112,260,3,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4332
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4333 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 7 152 144 106 106 234 362), lower := (rows 113 262 7 152 144 32 64 128 256), losses := [] }

theorem u4333 : Upper (D 1) (R 1) [112,260,3,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4333
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4334 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 13 138 18 240 240 240 496), lower := (rows 113 262 13 138 18 32 64 128 256), losses := [] }

theorem u4334 : Upper (D 1) (R 1) [112,260,9,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4334
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4335 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 13 138 48 242 210 210 466), lower := (rows 113 262 13 138 48 32 64 128 256), losses := [] }

theorem u4335 : Upper (D 1) (R 1) [112,260,9,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4335
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4336_2 : Upper (D 1) (R 1) [112,260,9,130,128,2] 13 :=
  permutation_upper _ _ _ [112,260,9,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1165

theorem m4336_16 : Upper (D 1) (R 1) [112,260,9,130,128,16] 13 :=
  permutation_upper _ _ _ [112,260,9,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1166

theorem m4336_64 : Upper (D 1) (R 1) [112,260,9,130,128,64] 13 :=
  permutation_upper _ _ _ [112,260,9,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1167

def r4336 : Route 9 := (fun mask => (mask,id))

def c4336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4336 : Upper (D 1) (R 1) [112,260,9,130,128] 13 := by
  apply FastRouting.sound _ _ [112,260,9,130,128] 13 (by decide) (choices 1) [2,16,64] r4336 c4336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4336_2
  · exact m4336_16
  · exact m4336_64

def b4337 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 14 137 18 240 240 240 496), lower := (rows 113 262 14 137 18 32 64 128 256), losses := [] }

theorem u4337 : Upper (D 1) (R 1) [112,260,10,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4337
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4338 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 14 137 48 242 210 210 466), lower := (rows 113 262 14 137 48 32 64 128 256), losses := [] }

theorem u4338 : Upper (D 1) (R 1) [112,260,10,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4338
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4339_2 : Upper (D 1) (R 1) [112,260,10,129,128,2] 13 :=
  permutation_upper _ _ _ [112,260,10,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1168

theorem m4339_16 : Upper (D 1) (R 1) [112,260,10,129,128,16] 13 :=
  permutation_upper _ _ _ [112,260,10,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1169

theorem m4339_64 : Upper (D 1) (R 1) [112,260,10,129,128,64] 13 :=
  permutation_upper _ _ _ [112,260,10,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1170

def r4339 : Route 9 := (fun mask => (mask,id))

def c4339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4339 : Upper (D 1) (R 1) [112,260,10,129,128] 13 := by
  apply FastRouting.sound _ _ [112,260,10,129,128] 13 (by decide) (choices 1) [2,16,64] r4339 c4339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4339_2
  · exact m4339_16
  · exact m4339_64

def b4340 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 262 14 152 17 226 226 226 482), lower := (rows 113 262 14 152 17 32 64 128 256), losses := [] }

theorem u4340 : Upper (D 1) (R 1) [112,260,10,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4340
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4341 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 14 152 18 225 225 225 481), lower := (rows 113 262 14 152 18 32 64 128 256), losses := [] }

theorem u4341 : Upper (D 1) (R 1) [112,260,10,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4341
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4342 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 14 152 48 227 195 195 451), lower := (rows 113 262 14 152 48 32 64 128 256), losses := [] }

theorem u4342 : Upper (D 1) (R 1) [112,260,10,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4342
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4343 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 14 152 144 99 99 227 355), lower := (rows 113 262 14 152 144 32 64 128 256), losses := [] }

theorem u4343 : Upper (D 1) (R 1) [112,260,10,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4343
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4344 : PairBound 9 := { available := 232, camps := [{ cop := 8, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 22 137 18 232 232 232 488), lower := (rows 113 262 22 137 18 32 64 128 256), losses := [] }

theorem u4344 : Upper (D 1) (R 1) [112,260,18,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4344
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4345 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 262 22 137 24 226 226 226 482), lower := (rows 113 262 22 137 24 32 64 128 256), losses := [] }

theorem u4345 : Upper (D 1) (R 1) [112,260,18,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4346 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 22 137 48 234 202 202 458), lower := (rows 113 262 22 137 48 32 64 128 256), losses := [] }

theorem u4346 : Upper (D 1) (R 1) [112,260,18,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4346
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4347 : Route 9 := (fun mask => (mask,id))

def c4347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4347 : Upper (D 1) (R 1) [112,260,18,129,128] 13 := by
  apply FastRouting.sound _ _ [112,260,18,129,128] 13 (by decide) (choices 1) [2,8,64] r4347 c4347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1171
  · exact u1172
  · exact u1173

def b4348 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 262 22 168 17 234 202 202 458), lower := (rows 113 262 22 168 17 32 64 128 256), losses := [] }

theorem u4348 : Upper (D 1) (R 1) [112,260,18,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4348
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4349 : PairBound 9 := { available := 201, camps := [{ cop := 8, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 22 168 18 233 201 201 457), lower := (rows 113 262 22 168 18 32 64 128 256), losses := [] }

theorem u4349 : Upper (D 1) (R 1) [112,260,18,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4349
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4350 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 262 22 168 24 227 195 195 451), lower := (rows 113 262 22 168 24 32 64 128 256), losses := [] }

theorem u4350 : Upper (D 1) (R 1) [112,260,18,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4350
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4351 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 22 168 80 171 203 139 395), lower := (rows 113 262 22 168 80 32 64 128 256), losses := [] }

theorem u4351 : Upper (D 1) (R 1) [112,260,18,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4351
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4352 : Route 9 := (fun mask => (mask,id))

def c4352 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4352 : Upper (D 1) (R 1) [112,260,18,160,128] 13 := by
  apply FastRouting.sound _ _ [112,260,18,160,128] 13 (by decide) (choices 1) [1,2,8,64] r4352 c4352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1174
  · exact u1175
  · exact u1176
  · exact u1177

def b4353 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 262 28 42 17 226 194 194 450), lower := (rows 113 262 28 42 17 32 64 128 256), losses := [] }

theorem u4353 : Upper (D 1) (R 1) [112,260,24,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4353
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4354 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 262 28 42 18 225 193 193 449), lower := (rows 113 262 28 42 18 32 64 128 256), losses := [] }

theorem u4354 : Upper (D 1) (R 1) [112,260,24,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4354
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4355 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 28 42 80 163 195 131 387), lower := (rows 113 262 28 42 80 32 64 128 256), losses := [] }

theorem u4355 : Upper (D 1) (R 1) [112,260,24,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4355
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4356 : Route 9 := (fun mask => (mask,id))

def c4356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4356 : Upper (D 1) (R 1) [112,260,24,34,128] 13 := by
  apply FastRouting.sound _ _ [112,260,24,34,128] 13 (by decide) (choices 1) [1,2,64,128] r4356 c4356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1178
  · exact u1179
  · exact u1180
  · exact u1181

def b4357 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 262 28 138 17 226 226 226 482), lower := (rows 113 262 28 138 17 32 64 128 256), losses := [] }

theorem u4357 : Upper (D 1) (R 1) [112,260,24,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4357
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4358 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 262 28 138 18 225 225 225 481), lower := (rows 113 262 28 138 18 32 64 128 256), losses := [] }

theorem u4358 : Upper (D 1) (R 1) [112,260,24,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4358
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4359 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 28 138 48 227 195 195 451), lower := (rows 113 262 28 138 48 32 64 128 256), losses := [] }

theorem u4359 : Upper (D 1) (R 1) [112,260,24,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4359
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4360 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 28 138 144 99 99 227 355), lower := (rows 113 262 28 138 144 32 64 128 256), losses := [] }

theorem u4360 : Upper (D 1) (R 1) [112,260,24,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4360
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4361 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 262 28 168 17 226 194 194 450), lower := (rows 113 262 28 168 17 32 64 128 256), losses := [] }

theorem u4361 : Upper (D 1) (R 1) [112,260,24,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4361
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4362 : Route 9 := (fun mask => (mask,id))

def c4362 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4362 : Upper (D 1) (R 1) [112,260,24,160,2] 13 := by
  apply FastRouting.sound _ _ [112,260,24,160,2] 13 (by decide) (choices 1) [1,2,64,128] r4362 c4362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1182
  · exact u1183
  · exact u1184
  · exact u1185

def b4363 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 28 168 80 163 195 131 387), lower := (rows 113 262 28 168 80 32 64 128 256), losses := [] }

theorem u4363 : Upper (D 1) (R 1) [112,260,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4363
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4364 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 28 168 144 99 67 195 323), lower := (rows 113 262 28 168 144 32 64 128 256), losses := [] }

theorem u4364 : Upper (D 1) (R 1) [112,260,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4364
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4365 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 262 133 26 18 232 232 232 488), lower := (rows 113 262 133 26 18 32 64 128 256), losses := [] }

theorem u4365 : Upper (D 1) (R 1) [112,260,129,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4365
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4366 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 262 133 26 24 226 226 226 482), lower := (rows 113 262 133 26 24 32 64 128 256), losses := [] }

theorem u4366 : Upper (D 1) (R 1) [112,260,129,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4366
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4367 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 133 26 48 234 202 202 458), lower := (rows 113 262 133 26 48 32 64 128 256), losses := [] }

theorem u4367 : Upper (D 1) (R 1) [112,260,129,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4367
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4368 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 133 26 144 106 106 234 362), lower := (rows 113 262 133 26 144 32 64 128 256), losses := [] }

theorem u4368 : Upper (D 1) (R 1) [112,260,129,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4368
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4369 : Route 9 := (fun mask => (mask,id))

def c4369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4369 : Upper (D 1) (R 1) [112,260,129,144,2] 13 := by
  apply FastRouting.sound _ _ [112,260,129,144,2] 13 (by decide) (choices 1) [2,8,64] r4369 c4369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1186
  · exact u1187
  · exact u1188

def b4370 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 262 133 152 24 98 98 226 354), lower := (rows 113 262 133 152 24 32 64 128 256), losses := [] }

theorem u4370 : Upper (D 1) (R 1) [112,260,129,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4370
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4371 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 133 152 48 106 74 202 330), lower := (rows 113 262 133 152 48 32 64 128 256), losses := [] }

theorem u4371 : Upper (D 1) (R 1) [112,260,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4371
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4372 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 134 137 18 120 120 248 376), lower := (rows 113 262 134 137 18 32 64 128 256), losses := [] }

theorem u4372 : Upper (D 1) (R 1) [112,260,130,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4372
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4373 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 113 262 134 137 24 114 114 242 370), lower := (rows 113 262 134 137 24 32 64 128 256), losses := [] }

theorem u4373 : Upper (D 1) (R 1) [112,260,130,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4373
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4374 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 134 137 48 122 90 218 346), lower := (rows 113 262 134 137 48 32 64 128 256), losses := [] }

theorem u4374 : Upper (D 1) (R 1) [112,260,130,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4374
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4375 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 262 134 152 17 106 106 234 362), lower := (rows 113 262 134 152 17 32 64 128 256), losses := [] }

theorem u4375 : Upper (D 1) (R 1) [112,260,130,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4375
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4376 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 262 134 152 18 105 105 233 361), lower := (rows 113 262 134 152 18 32 64 128 256), losses := [] }

theorem u4376 : Upper (D 1) (R 1) [112,260,130,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4376
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4377 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 262 134 152 24 99 99 227 355), lower := (rows 113 262 134 152 24 32 64 128 256), losses := [] }

theorem u4377 : Upper (D 1) (R 1) [112,260,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4377
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4378 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 134 152 48 107 75 203 331), lower := (rows 113 262 134 152 48 32 64 128 256), losses := [] }

theorem u4378 : Upper (D 1) (R 1) [112,260,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4378
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4379 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 140 11 18 240 240 240 496), lower := (rows 113 262 140 11 18 32 64 128 256), losses := [] }

theorem u4379 : Upper (D 1) (R 1) [112,260,136,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4379
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4379
end Delivery.IrregularNine14.P01
