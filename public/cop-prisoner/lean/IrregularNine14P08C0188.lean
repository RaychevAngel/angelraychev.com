import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0056
import IrregularNine14P08C0057

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11280 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 304 248 216 216 472), lower := (rows 67 134 37 41 304 32 64 128 256), losses := [] }

theorem u11280 : Upper (D 8) (R 8) [66,132,33,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11281 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 336 184 248 184 440), lower := (rows 67 134 37 41 336 32 64 128 256), losses := [] }

theorem u11281 : Upper (D 8) (R 8) [66,132,33,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11282 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 37 41 400 120 120 248 376), lower := (rows 67 134 37 41 400 32 64 128 256), losses := [] }

theorem u11282 : Upper (D 8) (R 8) [66,132,33,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11283 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 56 56 481 449 449 449), lower := (rows 67 134 37 56 56 32 64 128 256), losses := [] }

theorem u11283 : Upper (D 8) (R 8) [66,132,33,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11284 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 56 81 424 488 424 424), lower := (rows 67 134 37 56 81 32 64 128 256), losses := [] }

theorem u11284 : Upper (D 8) (R 8) [66,132,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11285 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 56 88 417 481 417 417), lower := (rows 67 134 37 56 88 32 64 128 256), losses := [] }

theorem u11285 : Upper (D 8) (R 8) [66,132,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11286 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 56 112 425 457 393 393), lower := (rows 67 134 37 56 112 32 64 128 256), losses := [] }

theorem u11286 : Upper (D 8) (R 8) [66,132,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11287 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 37 56 145 360 360 488 360), lower := (rows 67 134 37 56 145 32 64 128 256), losses := [] }

theorem u11287 : Upper (D 8) (R 8) [66,132,33,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11288 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 37 56 152 353 353 481 353), lower := (rows 67 134 37 56 152 32 64 128 256), losses := [] }

theorem u11288 : Upper (D 8) (R 8) [66,132,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11289 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 56 176 361 329 457 329), lower := (rows 67 134 37 56 176 32 64 128 256), losses := [] }

theorem u11289 : Upper (D 8) (R 8) [66,132,33,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11290 : Route 9 := (fun mask => (mask,id))

def c11290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11290 : Upper (D 8) (R 8) [66,132,33,48,192] 13 := by
  apply FastRouting.sound _ _ [66,132,33,48,192] 13 (by decide) (choices 1) [1,8,256] r11290 c11290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3388
  · exact u3389
  · exact u3390

def b11291 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 56 273 232 232 232 488), lower := (rows 67 134 37 56 273 32 64 128 256), losses := [] }

theorem u11291 : Upper (D 8) (R 8) [66,132,33,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11292 : Route 9 := (fun mask => (mask,id))

def c11292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11292 : Upper (D 8) (R 8) [66,132,33,48,264] 13 := by
  apply FastRouting.sound _ _ [66,132,33,48,264] 13 (by decide) (choices 1) [1,64,128] r11292 c11292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3391
  · exact u3392
  · exact u3393

def b11293 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 56 304 233 201 201 457), lower := (rows 67 134 37 56 304 32 64 128 256), losses := [] }

theorem u11293 : Upper (D 8) (R 8) [66,132,33,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11294 : Route 9 := (fun mask => (mask,id))

def c11294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11294 : Upper (D 8) (R 8) [66,132,33,48,320] 13 := by
  apply FastRouting.sound _ _ [66,132,33,48,320] 13 (by decide) (choices 1) [1,8,128] r11294 c11294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3394
  · exact u3395
  · exact u3396

def r11295 : Route 9 := (fun mask => (mask,id))

def c11295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11295 : Upper (D 8) (R 8) [66,132,33,48,384] 13 := by
  apply FastRouting.sound _ _ [66,132,33,48,384] 13 (by decide) (choices 1) [1,8,64] r11295 c11295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3397
  · exact u3398
  · exact u3399

def b11296 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 73 152 304 368 432 304), lower := (rows 67 134 37 73 152 32 64 128 256), losses := [] }

theorem u11296 : Upper (D 8) (R 8) [66,132,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11297 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 73 176 312 376 440 312), lower := (rows 67 134 37 73 176 32 64 128 256), losses := [] }

theorem u11297 : Upper (D 8) (R 8) [66,132,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11298 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 73 280 176 240 176 432), lower := (rows 67 134 37 73 280 32 64 128 256), losses := [] }

theorem u11298 : Upper (D 8) (R 8) [66,132,33,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11299 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 73 304 184 248 184 440), lower := (rows 67 134 37 73 304 32 64 128 256), losses := [] }

theorem u11299 : Upper (D 8) (R 8) [66,132,33,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11300 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 73 400 56 120 184 312), lower := (rows 67 134 37 73 400 32 64 128 256), losses := [] }

theorem u11300 : Upper (D 8) (R 8) [66,132,33,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11301 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 37 88 145 296 360 424 296), lower := (rows 67 134 37 88 145 32 64 128 256), losses := [] }

theorem u11301 : Upper (D 8) (R 8) [66,132,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11302 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 88 152 289 353 417 289), lower := (rows 67 134 37 88 152 32 64 128 256), losses := [] }

theorem u11302 : Upper (D 8) (R 8) [66,132,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11303 : Route 9 := (fun mask => (mask,id))

def c11303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11303 : Upper (D 8) (R 8) [66,132,33,80,160] 13 := by
  apply FastRouting.sound _ _ [66,132,33,80,160] 13 (by decide) (choices 1) [1,8,256] r11303 c11303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3400
  · exact u3401
  · exact u3402

def b11304 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 88 273 168 232 168 424), lower := (rows 67 134 37 88 273 32 64 128 256), losses := [] }

theorem u11304 : Upper (D 8) (R 8) [66,132,33,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11305 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 88 280 161 225 161 417), lower := (rows 67 134 37 88 280 32 64 128 256), losses := [] }

theorem u11305 : Upper (D 8) (R 8) [66,132,33,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11306 : Route 9 := (fun mask => (mask,id))

def c11306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11306 : Upper (D 8) (R 8) [66,132,33,80,288] 13 := by
  apply FastRouting.sound _ _ [66,132,33,80,288] 13 (by decide) (choices 1) [1,8,128] r11306 c11306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3403
  · exact u3404
  · exact u3405

def r11307 : Route 9 := (fun mask => (mask,id))

def c11307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11307 : Upper (D 8) (R 8) [66,132,33,80,384] 13 := by
  apply FastRouting.sound _ _ [66,132,33,80,384] 13 (by decide) (choices 1) [1,8] r11307 c11307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3406
  · exact u3407

def b11308 : PairBound 9 := { available := 312, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 37 104 145 312 376 440 312), lower := (rows 67 134 37 104 145 32 64 128 256), losses := [] }

theorem u11308 : Upper (D 8) (R 8) [66,132,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11309 : Route 9 := (fun mask => (mask,id))

def c11309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11309 : Upper (D 8) (R 8) [66,132,33,96,136] 13 := by
  apply FastRouting.sound _ _ [66,132,33,96,136] 13 (by decide) (choices 1) [1,16,256] r11309 c11309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3408
  · exact u3409
  · exact u3410

def r11310 : Route 9 := (fun mask => (mask,id))

def c11310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11310 : Upper (D 8) (R 8) [66,132,33,96,160] 13 := by
  apply FastRouting.sound _ _ [66,132,33,96,160] 13 (by decide) (choices 1) [1,8,16,256] r11310 c11310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3411
  · exact u3412
  · exact u3413
  · exact u3414

def b11311 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 104 273 184 248 184 440), lower := (rows 67 134 37 104 273 32 64 128 256), losses := [] }

theorem u11311 : Upper (D 8) (R 8) [66,132,33,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11312 : Route 9 := (fun mask => (mask,id))

def c11312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11312 : Upper (D 8) (R 8) [66,132,33,96,264] 13 := by
  apply FastRouting.sound _ _ [66,132,33,96,264] 13 (by decide) (choices 1) [1,16,128] r11312 c11312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3415
  · exact u3416
  · exact u3417

def r11313 : Route 9 := (fun mask => (mask,id))

def c11313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11313 : Upper (D 8) (R 8) [66,132,33,96,288] 13 := by
  apply FastRouting.sound _ _ [66,132,33,96,288] 13 (by decide) (choices 1) [1,8,16,128] r11313 c11313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3418
  · exact u3419
  · exact u3420
  · exact u3421

def r11314 : Route 9 := (fun mask => (mask,id))

def c11314 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11314 : Upper (D 8) (R 8) [66,132,33,96,384] 13 := by
  apply FastRouting.sound _ _ [66,132,33,96,384] 13 (by decide) (choices 1) [1,8,16] r11314 c11314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3422
  · exact u3423
  · exact u3424

def b11315 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 37 137 280 112 112 240 368), lower := (rows 67 134 37 137 280 32 64 128 256), losses := [] }

theorem u11315 : Upper (D 8) (R 8) [66,132,33,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11316 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 37 137 304 120 120 248 376), lower := (rows 67 134 37 137 304 32 64 128 256), losses := [] }

theorem u11316 : Upper (D 8) (R 8) [66,132,33,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11317 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 37 137 336 56 120 184 312), lower := (rows 67 134 37 137 336 32 64 128 256), losses := [] }

theorem u11317 : Upper (D 8) (R 8) [66,132,33,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11318 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 152 273 104 104 232 360), lower := (rows 67 134 37 152 273 32 64 128 256), losses := [] }

theorem u11318 : Upper (D 8) (R 8) [66,132,33,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11319 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 37 152 280 97 97 225 353), lower := (rows 67 134 37 152 280 32 64 128 256), losses := [] }

theorem u11319 : Upper (D 8) (R 8) [66,132,33,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11320 : Route 9 := (fun mask => (mask,id))

def c11320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11320 : Upper (D 8) (R 8) [66,132,33,144,288] 13 := by
  apply FastRouting.sound _ _ [66,132,33,144,288] 13 (by decide) (choices 1) [1,8,64] r11320 c11320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3425
  · exact u3426
  · exact u3427

def r11321 : Route 9 := (fun mask => (mask,id))

def c11321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11321 : Upper (D 8) (R 8) [66,132,33,144,320] 13 := by
  apply FastRouting.sound _ _ [66,132,33,144,320] 13 (by decide) (choices 1) [1,8] r11321 c11321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3428
  · exact u3429

def b11322 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 168 273 120 120 248 376), lower := (rows 67 134 37 168 273 32 64 128 256), losses := [] }

theorem u11322 : Upper (D 8) (R 8) [66,132,33,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11323 : Route 9 := (fun mask => (mask,id))

def c11323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11323 : Upper (D 8) (R 8) [66,132,33,160,264] 13 := by
  apply FastRouting.sound _ _ [66,132,33,160,264] 13 (by decide) (choices 1) [1,16,64] r11323 c11323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3430
  · exact u3431
  · exact u3432

def r11324 : Route 9 := (fun mask => (mask,id))

def c11324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11324 : Upper (D 8) (R 8) [66,132,33,160,288] 13 := by
  apply FastRouting.sound _ _ [66,132,33,160,288] 13 (by decide) (choices 1) [1,8,16,64] r11324 c11324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3433
  · exact u3434
  · exact u3435
  · exact u3436

def r11325 : Route 9 := (fun mask => (mask,id))

def c11325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11325 : Upper (D 8) (R 8) [66,132,33,160,320] 13 := by
  apply FastRouting.sound _ _ [66,132,33,160,320] 13 (by decide) (choices 1) [1,8,16] r11325 c11325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3437
  · exact u3438
  · exact u3439

def b11326 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 37 200 273 56 120 184 312), lower := (rows 67 134 37 200 273 32 64 128 256), losses := [] }

theorem u11326 : Upper (D 8) (R 8) [66,132,33,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11327 : Route 9 := (fun mask => (mask,id))

def c11327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11327 : Upper (D 8) (R 8) [66,132,33,192,264] 13 := by
  apply FastRouting.sound _ _ [66,132,33,192,264] 13 (by decide) (choices 1) [1,16] r11327 c11327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3440
  · exact u3441

def r11328 : Route 9 := (fun mask => (mask,id))

def c11328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11328 : Upper (D 8) (R 8) [66,132,33,192,288] 13 := by
  apply FastRouting.sound _ _ [66,132,33,192,288] 13 (by decide) (choices 1) [1,8,16] r11328 c11328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3442
  · exact u3443
  · exact u3444

def b11329 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 134 44 25 49 480 480 480 480), lower := (rows 67 134 44 25 49 32 64 128 256), losses := [] }

theorem u11329 : Upper (D 8) (R 8) [66,132,40,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11330 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 44 25 81 416 480 416 416), lower := (rows 67 134 44 25 81 32 64 128 256), losses := [] }

theorem u11330 : Upper (D 8) (R 8) [66,132,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11331 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 44 25 112 417 481 417 417), lower := (rows 67 134 44 25 112 32 64 128 256), losses := [] }

theorem u11331 : Upper (D 8) (R 8) [66,132,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11332 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 44 25 145 352 352 480 352), lower := (rows 67 134 44 25 145 32 64 128 256), losses := [] }

theorem u11332 : Upper (D 8) (R 8) [66,132,40,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11333 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 44 25 176 353 353 481 353), lower := (rows 67 134 44 25 176 32 64 128 256), losses := [] }

theorem u11333 : Upper (D 8) (R 8) [66,132,40,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11334 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 44 25 208 289 353 417 289), lower := (rows 67 134 44 25 208 32 64 128 256), losses := [] }

theorem u11334 : Upper (D 8) (R 8) [66,132,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11335 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 44 25 273 224 224 224 480), lower := (rows 67 134 44 25 273 32 64 128 256), losses := [] }

theorem u11335 : Upper (D 8) (R 8) [66,132,40,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11336 : Route 9 := (fun mask => (mask,id))

def c11336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11336 : Upper (D 8) (R 8) [66,132,40,17,288] 13 := by
  apply FastRouting.sound _ _ [66,132,40,17,288] 13 (by decide) (choices 1) [1,64,128] r11336 c11336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3445
  · exact u3446
  · exact u3447

def b11337 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 44 25 336 161 225 161 417), lower := (rows 67 134 44 25 336 32 64 128 256), losses := [] }

theorem u11337 : Upper (D 8) (R 8) [66,132,40,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11338 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 44 25 400 97 97 225 353), lower := (rows 67 134 44 25 400 32 64 128 256), losses := [] }

theorem u11338 : Upper (D 8) (R 8) [66,132,40,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11339 : Route 9 := (fun mask => (mask,id))

def c11339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u11339 : Upper (D 8) (R 8) [66,132,40,257,33] 13 := by
  apply FastRouting.sound _ _ [66,132,40,257,33] 13 (by decide) (choices 1) [16,64,128] r11339 c11339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3448
  · exact u3449
  · exact u3450

#print axioms u11339
end Delivery.IrregularNine14.P08
