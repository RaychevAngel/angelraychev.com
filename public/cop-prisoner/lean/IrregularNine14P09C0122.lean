import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0069
import IrregularNine14P09C0070
import IrregularNine14P09C0071

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7320 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 67 76 152 148 289 353 417 289), lower := (rows 35 67 76 152 148 32 64 128 256), losses := [] }

theorem u7320 : Upper (D 9) (R 9) [34,65,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7320 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7321 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 67 76 152 176 293 325 389 261), lower := (rows 35 67 76 152 176 32 64 128 256), losses := [] }

theorem u7321 : Upper (D 9) (R 9) [34,65,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7321 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7322 : Route 9 := (fun mask => (mask,id))

def c7322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7322 : Upper (D 9) (R 9) [34,65,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,257] 13 (by decide) (choices 1) [4,128,256] r7322 c7322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4171
  · exact u4172
  · exact u4173

def r7323 : Route 9 := (fun mask => (mask,id))

def c7323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7323 : Upper (D 9) (R 9) [34,65,72,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,260] 13 (by decide) (choices 1) [1,128,256] r7323 c7323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4174
  · exact u4175
  · exact u4176

def r7324 : Route 9 := (fun mask => (mask,id))

def c7324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7324 : Upper (D 9) (R 9) [34,65,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,288] 13 (by decide) (choices 1) [1,4,128,256] r7324 c7324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4177
  · exact u4178
  · exact u4179
  · exact u4180

def b7325 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 67 76 152 400 293 357 421 293), lower := (rows 35 67 76 152 400 32 64 128 256), losses := [] }

theorem u7325 : Upper (D 9) (R 9) [34,65,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7325 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7326 : Route 9 := (fun mask => (mask,id))

def c7326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7326 : Upper (D 9) (R 9) [34,65,72,160,129] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,129] 13 (by decide) (choices 1) [4,16,256] r7326 c7326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4181
  · exact u4182
  · exact u4183

def r7327 : Route 9 := (fun mask => (mask,id))

def c7327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7327 : Upper (D 9) (R 9) [34,65,72,160,132] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,132] 13 (by decide) (choices 1) [1,16,256] r7327 c7327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4184
  · exact u4185
  · exact u4186

def r7328 : Route 9 := (fun mask => (mask,id))

def c7328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7328 : Upper (D 9) (R 9) [34,65,72,160,257] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,257] 13 (by decide) (choices 1) [4,16,128,256] r7328 c7328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4187
  · exact u4188
  · exact u4189
  · exact u4190

def r7329 : Route 9 := (fun mask => (mask,id))

def c7329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7329 : Upper (D 9) (R 9) [34,65,72,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,260] 13 (by decide) (choices 1) [1,16,128,256] r7329 c7329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4191
  · exact u4192
  · exact u4193
  · exact u4194

def r7330 : Route 9 := (fun mask => (mask,id))

def c7330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7330 : Upper (D 9) (R 9) [34,65,72,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,384] 13 (by decide) (choices 1) [1,4,16,256] r7330 c7330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4195
  · exact u4196
  · exact u4197
  · exact u4198

def r7331 : Route 9 := (fun mask => (mask,id))

def c7331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7331 : Upper (D 9) (R 9) [34,65,72,384,129] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,129] 13 (by decide) (choices 1) [4,16,256] r7331 c7331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4199
  · exact u4200
  · exact u4201

def r7332 : Route 9 := (fun mask => (mask,id))

def c7332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7332 : Upper (D 9) (R 9) [34,65,72,384,132] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,132] 13 (by decide) (choices 1) [1,16,256] r7332 c7332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4202
  · exact u4203
  · exact u4204

def r7333 : Route 9 := (fun mask => (mask,id))

def c7333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7333 : Upper (D 9) (R 9) [34,65,72,384,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,160] 13 (by decide) (choices 1) [1,4,16,256] r7333 c7333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4205
  · exact u4206
  · exact u4207
  · exact u4208

def b7334 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 67 76 392 400 53 117 181 309), lower := (rows 35 67 76 392 400 32 64 128 256), losses := [] }

theorem u7334 : Upper (D 9) (R 9) [34,65,72,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7334 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7335 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 3, targets := 384 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 100 137 148 312 344 408 280), lower := (rows 35 67 100 137 148 32 64 128 256), losses := [] }

theorem u7335 : Upper (D 9) (R 9) [34,65,96,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7335 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7336 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 3, targets := 384 },{ cop := 3, region := 16, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,5)], upper := (rows 35 67 100 137 152 308 340 404 276), lower := (rows 35 67 100 137 152 32 64 128 256), losses := [] }

theorem u7336 : Upper (D 9) (R 9) [34,65,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7336 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7337 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 384 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 100 137 276 440 472 408 408), lower := (rows 35 67 100 137 276 32 64 128 256), losses := [] }

theorem u7337 : Upper (D 9) (R 9) [34,65,96,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7337 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7338 : PairBound 9 := { available := 404, camps := [{ cop := 2, region := 3, targets := 384 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 100 137 280 436 468 404 404), lower := (rows 35 67 100 137 280 32 64 128 256), losses := [] }

theorem u7338 : Upper (D 9) (R 9) [34,65,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7338 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7339 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 3, targets := 384 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 100 137 400 316 348 412 284), lower := (rows 35 67 100 137 400 32 64 128 256), losses := [] }

theorem u7339 : Upper (D 9) (R 9) [34,65,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7339 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7340 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 3, targets := 384 },{ cop := 3, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,0)], upper := (rows 35 67 100 140 152 305 337 401 273), lower := (rows 35 67 100 140 152 32 64 128 256), losses := [] }

theorem u7340 : Upper (D 9) (R 9) [34,65,96,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7340 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7341 : Route 9 := (fun mask => (mask,id))

def c7341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7341 : Upper (D 9) (R 9) [34,65,96,132,264] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,264] 13 (by decide) (choices 1) [1,16,128,256] r7341 c7341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4209
  · exact u4210
  · exact u4211
  · exact u4212

def r7342 : Route 9 := (fun mask => (mask,id))

def c7342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7342 : Upper (D 9) (R 9) [34,65,96,132,384] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,384] 13 (by decide) (choices 1) [1,8,16,256] r7342 c7342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4213
  · exact u4214
  · exact u4215
  · exact u4216

def b7343 : PairBound 9 := { available := 261, camps := [{ cop := 7, region := 24, targets := 353 }], pairs := [(3,0),(3,5),(3,6),(3,8),(4,0)], upper := (rows 35 67 100 152 152 293 325 389 261), lower := (rows 35 67 100 152 152 32 64 128 256), losses := [] }

theorem u7343 : Upper (D 9) (R 9) [34,65,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7343 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m7344_256 : Upper (D 9) (R 9) [34,65,96,144,264,256] 13 :=
  permutation_upper _ _ _ [34,65,96,144,264,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4219

def r7344 : Route 9 := (fun mask => (mask,id))

def c7344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7344 : Upper (D 9) (R 9) [34,65,96,144,264] 13 := by
  apply FastRouting.sound _ _ [34,65,96,144,264] 13 (by decide) (choices 1) [1,4,128,256] r7344 c7344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4217
  · exact u4218
  · exact u4219
  · exact m7344_256

def b7345 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 3, targets := 384 },{ cop := 4, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,0)], upper := (rows 35 67 100 152 400 301 333 397 269), lower := (rows 35 67 100 152 400 32 64 128 256), losses := [] }

theorem u7345 : Upper (D 9) (R 9) [34,65,96,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7345 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7346 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 3, targets := 384 },{ cop := 3, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,0)], upper := (rows 35 67 100 392 400 61 93 157 285), lower := (rows 35 67 100 392 400 32 64 128 256), losses := [] }

theorem u7346 : Upper (D 9) (R 9) [34,65,96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7346 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7347 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(3,6),(3,8)], upper := (rows 35 67 133 140 280 368 368 496 368), lower := (rows 35 67 133 140 280 32 64 128 256), losses := [] }

theorem u7347 : Upper (D 9) (R 9) [34,65,129,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7347 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7348 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(3,6),(3,8)], upper := (rows 35 67 133 140 304 376 344 472 344), lower := (rows 35 67 133 140 304 32 64 128 256), losses := [] }

theorem u7348 : Upper (D 9) (R 9) [34,65,129,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7348 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7349 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 371, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(3,6),(3,8)], upper := (rows 35 67 133 140 336 312 376 440 312), lower := (rows 35 67 133 140 336 32 64 128 256), losses := [] }

theorem u7349 : Upper (D 9) (R 9) [34,65,129,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7349 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7350 : Route 9 := (fun mask => (mask,id))

def c7350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7350 : Upper (D 9) (R 9) [34,65,129,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,260] 13 (by decide) (choices 1) [8,64,256] r7350 c7350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4220
  · exact u4221
  · exact u4222

def r7351 : Route 9 := (fun mask => (mask,id))

def c7351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7351 : Upper (D 9) (R 9) [34,65,129,144,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,264] 13 (by decide) (choices 1) [4,64,256] r7351 c7351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4223
  · exact u4224
  · exact u4225

def r7352 : Route 9 := (fun mask => (mask,id))

def c7352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7352 : Upper (D 9) (R 9) [34,65,129,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,288] 13 (by decide) (choices 1) [4,8,64,256] r7352 c7352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4226
  · exact u4227
  · exact u4228
  · exact u4229

def r7353 : Route 9 := (fun mask => (mask,id))

def c7353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7353 : Upper (D 9) (R 9) [34,65,129,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,320] 13 (by decide) (choices 1) [4,8,256] r7353 c7353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4230
  · exact u4231
  · exact u4232

def r7354 : Route 9 := (fun mask => (mask,id))

def c7354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u7354 : Upper (D 9) (R 9) [34,65,129,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,260] 13 (by decide) (choices 1) [8,16,64,256] r7354 c7354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4233
  · exact u4234
  · exact u4235
  · exact u4236

def r7355 : Route 9 := (fun mask => (mask,id))

def c7355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7355 : Upper (D 9) (R 9) [34,65,129,160,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,264] 13 (by decide) (choices 1) [4,16,64,256] r7355 c7355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4237
  · exact u4238
  · exact u4239
  · exact u4240

def r7356 : Route 9 := (fun mask => (mask,id))

def c7356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7356 : Upper (D 9) (R 9) [34,65,129,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,320] 13 (by decide) (choices 1) [4,8,16,256] r7356 c7356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4241
  · exact u4242
  · exact u4243
  · exact u4244

def r7357 : Route 9 := (fun mask => (mask,id))

def c7357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7357 : Upper (D 9) (R 9) [34,65,129,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,260] 13 (by decide) (choices 1) [8,16,256] r7357 c7357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4245
  · exact u4246
  · exact u4247

def r7358 : Route 9 := (fun mask => (mask,id))

def c7358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7358 : Upper (D 9) (R 9) [34,65,129,192,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,264] 13 (by decide) (choices 1) [4,16,256] r7358 c7358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4248
  · exact u4249
  · exact u4250

def r7359 : Route 9 := (fun mask => (mask,id))

def c7359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7359 : Upper (D 9) (R 9) [34,65,129,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,288] 13 (by decide) (choices 1) [4,8,16,256] r7359 c7359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4251
  · exact u4252
  · exact u4253
  · exact u4254

def b7360 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8),(4,5),(4,6),(4,7)], upper := (rows 35 67 133 268 280 240 240 240 496), lower := (rows 35 67 133 268 280 32 64 128 256), losses := [] }

theorem u7360 : Upper (D 9) (R 9) [34,65,129,260,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7360 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7361 : Route 9 := (fun mask => (mask,id))

def c7361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7361 : Upper (D 9) (R 9) [34,65,129,260,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,288] 13 (by decide) (choices 1) [8,16,64,128] r7361 c7361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4255
  · exact u4256
  · exact u4257
  · exact u4258

def r7362 : Route 9 := (fun mask => (mask,id))

def c7362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7362 : Upper (D 9) (R 9) [34,65,129,260,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,320] 13 (by decide) (choices 1) [8,16,128] r7362 c7362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4259
  · exact u4260
  · exact u4261

def r7363 : Route 9 := (fun mask => (mask,id))

def c7363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7363 : Upper (D 9) (R 9) [34,65,129,260,384] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,384] 13 (by decide) (choices 1) [8,16,64] r7363 c7363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4262
  · exact u4263
  · exact u4264

def b7364 : PairBound 9 := { available := 228, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 35 67 133 280 280 228 228 228 484), lower := (rows 35 67 133 280 280 32 64 128 256), losses := [] }

theorem u7364 : Upper (D 9) (R 9) [34,65,129,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7364 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7365 : PairBound 9 := { available := 204, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 67 133 280 304 236 204 204 460), lower := (rows 35 67 133 280 304 32 64 128 256), losses := [] }

theorem u7365 : Upper (D 9) (R 9) [34,65,129,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7365 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7366 : PairBound 9 := { available := 172, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 67 133 280 336 172 236 172 428), lower := (rows 35 67 133 280 336 32 64 128 256), losses := [] }

theorem u7366 : Upper (D 9) (R 9) [34,65,129,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7366 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7367 : PairBound 9 := { available := 108, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 67 133 280 400 108 108 236 364), lower := (rows 35 67 133 280 400 32 64 128 256), losses := [] }

theorem u7367 : Upper (D 9) (R 9) [34,65,129,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7367 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7368 : Route 9 := (fun mask => (mask,id))

def c7368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7368 : Upper (D 9) (R 9) [34,65,129,288,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288,320] 13 (by decide) (choices 1) [4,8,16,128] r7368 c7368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4265
  · exact u4266
  · exact u4267
  · exact u4268

def r7369 : Route 9 := (fun mask => (mask,id))

def c7369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7369 : Upper (D 9) (R 9) [34,65,129,288,384] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288,384] 13 (by decide) (choices 1) [4,8,16,64] r7369 c7369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4269
  · exact u4270
  · exact u4271
  · exact u4272

def r7370 : Route 9 := (fun mask => (mask,id))

def c7370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7370 : Upper (D 9) (R 9) [34,65,129,320,384] 13 := by
  apply FastRouting.sound _ _ [34,65,129,320,384] 13 (by decide) (choices 1) [4,8,16] r7370 c7370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4273
  · exact u4274
  · exact u4275

def b7371 : PairBound 9 := { available := 337, camps := [{ cop := 7, region := 12, targets := 353 }], pairs := [(2,0),(2,5),(2,6),(2,8),(3,0)], upper := (rows 35 67 140 140 304 369 337 465 337), lower := (rows 35 67 140 140 304 32 64 128 256), losses := [] }

theorem u7371 : Upper (D 9) (R 9) [34,65,136,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7371 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7372 : PairBound 9 := { available := 305, camps := [{ cop := 7, region := 12, targets := 353 }], pairs := [(2,0),(2,5),(2,6),(2,8),(3,0)], upper := (rows 35 67 140 140 336 305 369 433 305), lower := (rows 35 67 140 140 336 32 64 128 256), losses := [] }

theorem u7372 : Upper (D 9) (R 9) [34,65,136,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7372 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7373 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 67 140 152 276 353 353 481 353), lower := (rows 35 67 140 152 276 32 64 128 256), losses := [] }

theorem u7373 : Upper (D 9) (R 9) [34,65,136,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7373 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7374 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 67 140 152 304 357 325 453 325), lower := (rows 35 67 140 152 304 32 64 128 256), losses := [] }

theorem u7374 : Upper (D 9) (R 9) [34,65,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7374 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7375 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 67 140 152 336 293 357 421 293), lower := (rows 35 67 140 152 336 32 64 128 256), losses := [] }

theorem u7375 : Upper (D 9) (R 9) [34,65,136,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7375 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7376 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 67 140 168 276 369 337 465 337), lower := (rows 35 67 140 168 276 32 64 128 256), losses := [] }

theorem u7376 : Upper (D 9) (R 9) [34,65,136,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7376 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7377 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 67 140 168 336 309 341 405 277), lower := (rows 35 67 140 168 336 32 64 128 256), losses := [] }

theorem u7377 : Upper (D 9) (R 9) [34,65,136,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7377 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7378 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 67 140 200 276 305 369 433 305), lower := (rows 35 67 140 200 276 32 64 128 256), losses := [] }

theorem u7378 : Upper (D 9) (R 9) [34,65,136,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7378 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7379 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 67 140 200 304 309 341 405 277), lower := (rows 35 67 140 200 304 32 64 128 256), losses := [] }

theorem u7379 : Upper (D 9) (R 9) [34,65,136,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7379 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u7379
end Delivery.IrregularNine14.P09
