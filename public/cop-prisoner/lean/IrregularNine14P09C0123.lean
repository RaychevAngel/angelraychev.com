import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0071
import IrregularNine14P09C0072
import IrregularNine14P09C0073

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7380 : Route 9 := (fun mask => (mask,id))

def c7380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7380 : Upper (D 9) (R 9) [34,65,136,260,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260,160] 13 (by decide) (choices 1) [1,16,64,256] r7380 c7380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4276
  · exact u4277
  · exact u4278
  · exact u4279

def r7381 : Route 9 := (fun mask => (mask,id))

def c7381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7381 : Upper (D 9) (R 9) [34,65,136,260,192] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260,192] 13 (by decide) (choices 1) [1,16,256] r7381 c7381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4280
  · exact u4281
  · exact u4282

def b7382 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0),(3,5)], upper := (rows 35 67 140 268 400 113 113 241 369), lower := (rows 35 67 140 268 400 32 64 128 256), losses := [] }

theorem u7382 : Upper (D 9) (R 9) [34,65,136,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7382 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7383 : Route 9 := (fun mask => (mask,id))

def c7383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7383 : Upper (D 9) (R 9) [34,65,136,272,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,160] 13 (by decide) (choices 1) [1,4,64,256] r7383 c7383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4283
  · exact u4284
  · exact u4285
  · exact u4286

def r7384 : Route 9 := (fun mask => (mask,id))

def c7384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7384 : Upper (D 9) (R 9) [34,65,136,272,192] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,192] 13 (by decide) (choices 1) [1,4,256] r7384 c7384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4287
  · exact u4288
  · exact u4289

def b7385 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0),(3,5)], upper := (rows 35 67 140 280 400 101 101 229 357), lower := (rows 35 67 140 280 400 32 64 128 256), losses := [] }

theorem u7385 : Upper (D 9) (R 9) [34,65,136,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7385 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7386 : Route 9 := (fun mask => (mask,id))

def c7386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7386 : Upper (D 9) (R 9) [34,65,136,288,192] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,192] 13 (by decide) (choices 1) [1,4,16,256] r7386 c7386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4290
  · exact u4291
  · exact u4292
  · exact u4293

def r7387 : Route 9 := (fun mask => (mask,id))

def c7387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7387 : Upper (D 9) (R 9) [34,65,136,288,320] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,320] 13 (by decide) (choices 1) [1,4,16,128] r7387 c7387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4294
  · exact u4295
  · exact u4296
  · exact u4297

def r7388 : Route 9 := (fun mask => (mask,id))

def c7388 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7388 : Upper (D 9) (R 9) [34,65,136,288,384] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,384] 13 (by decide) (choices 1) [1,4,16,64] r7388 c7388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4298
  · exact u4299
  · exact u4300
  · exact u4301

def r7389 : Route 9 := (fun mask => (mask,id))

def c7389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7389 : Upper (D 9) (R 9) [34,65,136,320,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,160] 13 (by decide) (choices 1) [1,4,16,256] r7389 c7389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4302
  · exact u4303
  · exact u4304
  · exact u4305

def r7390 : Route 9 := (fun mask => (mask,id))

def c7390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7390 : Upper (D 9) (R 9) [34,65,136,320,288] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,288] 13 (by decide) (choices 1) [1,4,16,128] r7390 c7390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4306
  · exact u4307
  · exact u4308
  · exact u4309

def r7391 : Route 9 := (fun mask => (mask,id))

def c7391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7391 : Upper (D 9) (R 9) [34,65,136,320,384] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,384] 13 (by decide) (choices 1) [1,4,16] r7391 c7391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4310
  · exact u4311
  · exact u4312

def b7392 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 67 140 392 304 117 85 213 341), lower := (rows 35 67 140 392 304 32 64 128 256), losses := [] }

theorem u7392 : Upper (D 9) (R 9) [34,65,136,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7392 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7393 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 67 140 392 336 53 117 181 309), lower := (rows 35 67 140 392 336 32 64 128 256), losses := [] }

theorem u7393 : Upper (D 9) (R 9) [34,65,136,384,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7393 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7394 : Route 9 := (fun mask => (mask,id))

def c7394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7394 : Upper (D 9) (R 9) [34,65,160,320,384] 13 := by
  apply FastRouting.sound _ _ [34,65,160,320,384] 13 (by decide) (choices 1) [1,4,8,16] r7394 c7394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4313
  · exact u4314
  · exact u4315
  · exact u4316

def b7395 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 428, targets := 64 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,6),(3,6),(4,5)], upper := (rows 35 70 13 56 81 416 448 384 384), lower := (rows 35 70 13 56 81 32 64 128 256), losses := [] }

theorem u7395 : Upper (D 9) (R 9) [34,68,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7395 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7396 : Route 9 := (fun mask => (mask,id))

def c7396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7396 : Upper (D 9) (R 9) [34,68,9,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,129] 13 (by decide) (choices 1) [64,128,256] r7396 c7396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4317
  · exact u4318
  · exact u4319

def r7397 : Route 9 := (fun mask => (mask,id))

def c7397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7397 : Upper (D 9) (R 9) [34,68,9,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,192] 13 (by decide) (choices 1) [1,128,256] r7397 c7397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4320
  · exact u4321
  · exact u4322

def r7398 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7398 : Upper (D 9) (R 9) [34,68,9,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,384] 13 (by decide) (choices 1) [1,64,128] r7398 c7398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4323
  · exact u4324
  · exact u4325

def b7399 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 70 13 88 49 416 448 384 384), lower := (rows 35 70 13 88 49 32 64 128 256), losses := [] }

theorem u7399 : Upper (D 9) (R 9) [34,68,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7399 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7400 : Route 9 := (fun mask => (mask,id))

def c7400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7400 : Upper (D 9) (R 9) [34,68,9,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,129] 13 (by decide) (choices 1) [128,256] r7400 c7400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4326
  · exact u4327

def r7401 : Route 9 := (fun mask => (mask,id))

def c7401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7401 : Upper (D 9) (R 9) [34,68,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,160] 13 (by decide) (choices 1) [1,128,256] r7401 c7401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4328
  · exact u4329
  · exact u4330

def r7402 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7402 : Upper (D 9) (R 9) [34,68,9,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80,384] 13 (by decide) (choices 1) [1,128] r7402 c7402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4331
  · exact u4332

def b7403 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 70 13 152 49 480 448 448 448), lower := (rows 35 70 13 152 49 32 64 128 256), losses := [] }

theorem u7403 : Upper (D 9) (R 9) [34,68,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7403 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7404 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 428, targets := 64 },{ cop := 1, region := 417, targets := 64 },{ cop := 2, region := 482, targets := 1 },{ cop := 4, region := 424, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0),(3,6)], upper := (rows 35 70 13 152 81 416 480 416 416), lower := (rows 35 70 13 152 81 32 64 128 256), losses := [] }

theorem u7404 : Upper (D 9) (R 9) [34,68,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7404 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7405 : Route 9 := (fun mask => (mask,id))

def c7405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7405 : Upper (D 9) (R 9) [34,68,9,144,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,96] 13 (by decide) (choices 1) [1,128,256] r7405 c7405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4333
  · exact u4334
  · exact u4335

def b7406 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 12, targets := 352 }], pairs := [(2,5),(2,6),(2,8),(3,5),(3,6)], upper := (rows 35 70 13 152 145 352 352 480 352), lower := (rows 35 70 13 152 145 32 64 128 256), losses := [] }

theorem u7406 : Upper (D 9) (R 9) [34,68,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7406 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7407 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 70 13 152 176 353 321 449 321), lower := (rows 35 70 13 152 176 32 64 128 256), losses := [] }

theorem u7407 : Upper (D 9) (R 9) [34,68,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7407 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7408 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 70 13 152 208 289 353 417 289), lower := (rows 35 70 13 152 208 32 64 128 256), losses := [] }

theorem u7408 : Upper (D 9) (R 9) [34,68,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7408 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7409 : Route 9 := (fun mask => (mask,id))

def c7409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7409 : Upper (D 9) (R 9) [34,68,9,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,257] 13 (by decide) (choices 1) [64,128,256] r7409 c7409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4336
  · exact u4337
  · exact u4338

def r7410 : Route 9 := (fun mask => (mask,id))

def c7410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7410 : Upper (D 9) (R 9) [34,68,9,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,288] 13 (by decide) (choices 1) [1,64,128,256] r7410 c7410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4339
  · exact u4340
  · exact u4341
  · exact u4342

def r7411 : Route 9 := (fun mask => (mask,id))

def c7411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7411 : Upper (D 9) (R 9) [34,68,9,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,320] 13 (by decide) (choices 1) [1,128,256] r7411 c7411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4343
  · exact u4344
  · exact u4345

def b7412 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 70 13 152 400 353 353 481 353), lower := (rows 35 70 13 152 400 32 64 128 256), losses := [] }

theorem u7412 : Upper (D 9) (R 9) [34,68,9,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7412 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7413 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 428, targets := 64 },{ cop := 4, region := 424, targets := 1 }], pairs := [(1,5),(2,6),(3,0),(3,6),(4,5)], upper := (rows 35 70 13 168 81 432 464 400 400), lower := (rows 35 70 13 168 81 32 64 128 256), losses := [] }

theorem u7413 : Upper (D 9) (R 9) [34,68,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7413 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7414 : Route 9 := (fun mask => (mask,id))

def c7414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7414 : Upper (D 9) (R 9) [34,68,9,160,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,129] 13 (by decide) (choices 1) [16,64,256] r7414 c7414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4346
  · exact u4347
  · exact u4348

def r7415 : Route 9 := (fun mask => (mask,id))

def c7415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7415 : Upper (D 9) (R 9) [34,68,9,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,192] 13 (by decide) (choices 1) [1,16,256] r7415 c7415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4349
  · exact u4350
  · exact u4351

def r7416 : Route 9 := (fun mask => (mask,id))

def c7416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7416 : Upper (D 9) (R 9) [34,68,9,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,257] 13 (by decide) (choices 1) [16,64,128,256] r7416 c7416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4352
  · exact u4353
  · exact u4354
  · exact u4355

def r7417 : Route 9 := (fun mask => (mask,id))

def c7417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7417 : Upper (D 9) (R 9) [34,68,9,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,320] 13 (by decide) (choices 1) [1,16,128,256] r7417 c7417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4356
  · exact u4357
  · exact u4358
  · exact u4359

def r7418 : Route 9 := (fun mask => (mask,id))

def c7418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7418 : Upper (D 9) (R 9) [34,68,9,160,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,384] 13 (by decide) (choices 1) [1,16,64,256] r7418 c7418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4360
  · exact u4361
  · exact u4362
  · exact u4363

def b7419 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 70 13 200 49 432 464 400 400), lower := (rows 35 70 13 200 49 32 64 128 256), losses := [] }

theorem u7419 : Upper (D 9) (R 9) [34,68,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7419 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7420 : Route 9 := (fun mask => (mask,id))

def c7420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7420 : Upper (D 9) (R 9) [34,68,9,192,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,129] 13 (by decide) (choices 1) [16,256] r7420 c7420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4364
  · exact u4365

def r7421 : Route 9 := (fun mask => (mask,id))

def c7421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7421 : Upper (D 9) (R 9) [34,68,9,192,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,160] 13 (by decide) (choices 1) [1,16,256] r7421 c7421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4366
  · exact u4367
  · exact u4368

def r7422 : Route 9 := (fun mask => (mask,id))

def c7422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7422 : Upper (D 9) (R 9) [34,68,9,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,257] 13 (by decide) (choices 1) [16,128,256] r7422 c7422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4369
  · exact u4370
  · exact u4371

def r7423 : Route 9 := (fun mask => (mask,id))

def c7423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7423 : Upper (D 9) (R 9) [34,68,9,192,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,288] 13 (by decide) (choices 1) [1,16,128,256] r7423 c7423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4372
  · exact u4373
  · exact u4374
  · exact u4375

def r7424 : Route 9 := (fun mask => (mask,id))

def c7424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7424 : Upper (D 9) (R 9) [34,68,9,192,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,384] 13 (by decide) (choices 1) [1,16,256] r7424 c7424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4376
  · exact u4377
  · exact u4378

def b7425 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 35 70 13 392 49 496 464 464 464), lower := (rows 35 70 13 392 49 32 64 128 256), losses := [] }

theorem u7425 : Upper (D 9) (R 9) [34,68,9,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7425 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7426 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7426 : Upper (D 9) (R 9) [34,68,9,384,65] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,65] 13 (by decide) (choices 1) [16,128] r7426 c7426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4379
  · exact u4380

def r7427 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7427 : Upper (D 9) (R 9) [34,68,9,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,96] 13 (by decide) (choices 1) [1,16,128] r7427 c7427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4381
  · exact u4382
  · exact u4383

def r7428 : Route 9 := (fun mask => (mask,id))

def c7428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7428 : Upper (D 9) (R 9) [34,68,9,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,129] 13 (by decide) (choices 1) [16,64,256] r7428 c7428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4384
  · exact u4385
  · exact u4386

def r7429 : Route 9 := (fun mask => (mask,id))

def c7429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7429 : Upper (D 9) (R 9) [34,68,9,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,160] 13 (by decide) (choices 1) [1,16,64,256] r7429 c7429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4387
  · exact u4388
  · exact u4389
  · exact u4390

def r7430 : Route 9 := (fun mask => (mask,id))

def c7430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7430 : Upper (D 9) (R 9) [34,68,9,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,192] 13 (by decide) (choices 1) [1,16,256] r7430 c7430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4391
  · exact u4392
  · exact u4393

def b7431 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 70 13 392 400 113 113 241 369), lower := (rows 35 70 13 392 400 32 64 128 256), losses := [] }

theorem u7431 : Upper (D 9) (R 9) [34,68,9,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7431 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7432 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 70 28 41 81 416 448 384 384), lower := (rows 35 70 28 41 81 32 64 128 256), losses := [] }

theorem u7432 : Upper (D 9) (R 9) [34,68,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7432 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7433 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 28 41 145 480 448 448 448), lower := (rows 35 70 28 41 145 32 64 128 256), losses := [] }

theorem u7433 : Upper (D 9) (R 9) [34,68,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7433 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7434 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 70 28 41 208 417 449 385 385), lower := (rows 35 70 28 41 208 32 64 128 256), losses := [] }

theorem u7434 : Upper (D 9) (R 9) [34,68,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7434 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7435 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 28 41 400 481 449 449 449), lower := (rows 35 70 28 41 400 32 64 128 256), losses := [] }

theorem u7435 : Upper (D 9) (R 9) [34,68,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7435 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7436 : Route 9 := (fun mask => (mask,id))

def c7436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7436 : Upper (D 9) (R 9) [34,68,24,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,24,65,129] 13 (by decide) (choices 1) [128,256] r7436 c7436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4394
  · exact u4395

def b7437 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 456, targets := 32 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(1,5),(2,6),(3,5),(4,6)], upper := (rows 35 70 28 73 176 417 449 385 385), lower := (rows 35 70 28 73 176 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 16 0 73 137 265), good := (rows 459 70 478 457 144 0 64 128 256) }] }

theorem u7437 : Upper (D 9) (R 9) [34,68,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7437 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7438 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7438 : Upper (D 9) (R 9) [34,68,24,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,65,384] 13 (by decide) (choices 1) [1,128] r7438 c7438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4396
  · exact u4397

def r7439 : Route 9 := (fun mask => (mask,id))

def c7439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7439 : Upper (D 9) (R 9) [34,68,24,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,24,96,129] 13 (by decide) (choices 1) [1,128,256] r7439 c7439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4398
  · exact u4399
  · exact u4400

#print axioms u7439
end Delivery.IrregularNine14.P09
