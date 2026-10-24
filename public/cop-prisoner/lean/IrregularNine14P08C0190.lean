import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0058

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11400 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 292 25 81 168 232 168 424), lower := (rows 67 134 292 25 81 32 64 128 256), losses := [] }

theorem u11400 : Upper (D 8) (R 8) [66,132,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11401 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 292 25 88 161 225 161 417), lower := (rows 67 134 292 25 88 32 64 128 256), losses := [] }

theorem u11401 : Upper (D 8) (R 8) [66,132,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11402 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 25 112 169 233 169 425), lower := (rows 67 134 292 25 112 32 64 128 256), losses := [] }

theorem u11402 : Upper (D 8) (R 8) [66,132,288,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11403 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 292 25 145 104 104 232 360), lower := (rows 67 134 292 25 145 32 64 128 256), losses := [] }

theorem u11403 : Upper (D 8) (R 8) [66,132,288,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11404 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 292 25 152 97 97 225 353), lower := (rows 67 134 292 25 152 32 64 128 256), losses := [] }

theorem u11404 : Upper (D 8) (R 8) [66,132,288,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11405 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 356, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 25 176 105 105 233 361), lower := (rows 67 134 292 25 176 32 64 128 256), losses := [] }

theorem u11405 : Upper (D 8) (R 8) [66,132,288,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11406 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 25 208 41 105 169 297), lower := (rows 67 134 292 25 208 32 64 128 256), losses := [] }

theorem u11406 : Upper (D 8) (R 8) [66,132,288,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11407 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 292 41 49 248 216 216 472), lower := (rows 67 134 292 41 49 32 64 128 256), losses := [] }

theorem u11407 : Upper (D 8) (R 8) [66,132,288,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11408 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 292 41 56 241 209 209 465), lower := (rows 67 134 292 41 56 32 64 128 256), losses := [] }

theorem u11408 : Upper (D 8) (R 8) [66,132,288,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11409 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 41 81 184 248 184 440), lower := (rows 67 134 292 41 81 32 64 128 256), losses := [] }

theorem u11409 : Upper (D 8) (R 8) [66,132,288,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11410 : Route 9 := (fun mask => (mask,id))

def c11410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11410 : Upper (D 8) (R 8) [66,132,288,33,72] 13 := by
  apply FastRouting.sound _ _ [66,132,288,33,72] 13 (by decide) (choices 1) [1,16,128] r11410 c11410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3484
  · exact u3485
  · exact u3486

def r11411 : Route 9 := (fun mask => (mask,id))

def c11411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11411 : Upper (D 8) (R 8) [66,132,288,33,96] 13 := by
  apply FastRouting.sound _ _ [66,132,288,33,96] 13 (by decide) (choices 1) [1,8,16,128] r11411 c11411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3487
  · exact u3488
  · exact u3489
  · exact u3490

def b11412 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 41 145 120 120 248 376), lower := (rows 67 134 292 41 145 32 64 128 256), losses := [] }

theorem u11412 : Upper (D 8) (R 8) [66,132,288,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11413 : Route 9 := (fun mask => (mask,id))

def c11413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11413 : Upper (D 8) (R 8) [66,132,288,33,136] 13 := by
  apply FastRouting.sound _ _ [66,132,288,33,136] 13 (by decide) (choices 1) [1,16,64] r11413 c11413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3491
  · exact u3492
  · exact u3493

def r11414 : Route 9 := (fun mask => (mask,id))

def c11414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11414 : Upper (D 8) (R 8) [66,132,288,33,160] 13 := by
  apply FastRouting.sound _ _ [66,132,288,33,160] 13 (by decide) (choices 1) [1,8,16,64] r11414 c11414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3494
  · exact u3495
  · exact u3496
  · exact u3497

def r11415 : Route 9 := (fun mask => (mask,id))

def c11415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11415 : Upper (D 8) (R 8) [66,132,288,33,192] 13 := by
  apply FastRouting.sound _ _ [66,132,288,33,192] 13 (by decide) (choices 1) [1,8,16] r11415 c11415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3498
  · exact u3499
  · exact u3500

def b11416 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 292 56 56 225 193 193 449), lower := (rows 67 134 292 56 56 32 64 128 256), losses := [] }

theorem u11416 : Upper (D 8) (R 8) [66,132,288,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11417 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 56 81 169 233 169 425), lower := (rows 67 134 292 56 81 32 64 128 256), losses := [] }

theorem u11417 : Upper (D 8) (R 8) [66,132,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11418 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 56 88 161 225 161 417), lower := (rows 67 134 292 56 88 32 64 128 256), losses := [] }

theorem u11418 : Upper (D 8) (R 8) [66,132,288,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11419 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 292 56 112 169 201 137 393), lower := (rows 67 134 292 56 112 32 64 128 256), losses := [] }

theorem u11419 : Upper (D 8) (R 8) [66,132,288,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11420 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 56 145 105 105 233 361), lower := (rows 67 134 292 56 145 32 64 128 256), losses := [] }

theorem u11420 : Upper (D 8) (R 8) [66,132,288,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11421 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 292 56 152 97 97 225 353), lower := (rows 67 134 292 56 152 32 64 128 256), losses := [] }

theorem u11421 : Upper (D 8) (R 8) [66,132,288,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11422 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 292 56 176 105 73 201 329), lower := (rows 67 134 292 56 176 32 64 128 256), losses := [] }

theorem u11422 : Upper (D 8) (R 8) [66,132,288,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11423 : Route 9 := (fun mask => (mask,id))

def c11423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11423 : Upper (D 8) (R 8) [66,132,288,48,192] 13 := by
  apply FastRouting.sound _ _ [66,132,288,48,192] 13 (by decide) (choices 1) [1,8] r11423 c11423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3501
  · exact u3502

def b11424 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 73 152 49 113 177 305), lower := (rows 67 134 292 73 152 32 64 128 256), losses := [] }

theorem u11424 : Upper (D 8) (R 8) [66,132,288,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11425 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 73 176 57 121 185 313), lower := (rows 67 134 292 73 176 32 64 128 256), losses := [] }

theorem u11425 : Upper (D 8) (R 8) [66,132,288,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11426 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 88 145 41 105 169 297), lower := (rows 67 134 292 88 145 32 64 128 256), losses := [] }

theorem u11426 : Upper (D 8) (R 8) [66,132,288,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11427 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 88 152 33 97 161 289), lower := (rows 67 134 292 88 152 32 64 128 256), losses := [] }

theorem u11427 : Upper (D 8) (R 8) [66,132,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11428 : Route 9 := (fun mask => (mask,id))

def c11428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11428 : Upper (D 8) (R 8) [66,132,288,80,160] 13 := by
  apply FastRouting.sound _ _ [66,132,288,80,160] 13 (by decide) (choices 1) [1,8] r11428 c11428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3503
  · exact u3504

def b11429 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 104 145 57 121 185 313), lower := (rows 67 134 292 104 145 32 64 128 256), losses := [] }

theorem u11429 : Upper (D 8) (R 8) [66,132,288,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11430 : Route 9 := (fun mask => (mask,id))

def c11430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11430 : Upper (D 8) (R 8) [66,132,288,96,136] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96,136] 13 (by decide) (choices 1) [1,16] r11430 c11430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3505
  · exact u3506

def r11431 : Route 9 := (fun mask => (mask,id))

def c11431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11431 : Upper (D 8) (R 8) [66,132,288,96,160] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96,160] 13 (by decide) (choices 1) [1,8,16] r11431 c11431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3507
  · exact u3508
  · exact u3509

def b11432 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 13 112 432 496 432 432), lower := (rows 67 162 13 13 112 32 64 128 256), losses := [] }

theorem u11432 : Upper (D 8) (R 8) [66,160,9,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11433 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 13 208 304 368 432 304), lower := (rows 67 162 13 13 208 32 64 128 256), losses := [] }

theorem u11433 : Upper (D 8) (R 8) [66,160,9,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11434 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 13 304 240 240 240 496), lower := (rows 67 162 13 13 304 32 64 128 256), losses := [] }

theorem u11434 : Upper (D 8) (R 8) [66,160,9,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11435 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 13 336 176 240 176 432), lower := (rows 67 162 13 13 336 32 64 128 256), losses := [] }

theorem u11435 : Upper (D 8) (R 8) [66,160,9,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11436 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 13 400 112 112 240 368), lower := (rows 67 162 13 13 400 32 64 128 256), losses := [] }

theorem u11436 : Upper (D 8) (R 8) [66,160,9,5,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11437 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 25 52 480 480 480 480), lower := (rows 67 162 13 25 52 32 64 128 256), losses := [] }

theorem u11437 : Upper (D 8) (R 8) [66,160,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11438 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 25 84 416 480 416 416), lower := (rows 67 162 13 25 84 32 64 128 256), losses := [] }

theorem u11438 : Upper (D 8) (R 8) [66,160,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11439 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 25 112 420 484 420 420), lower := (rows 67 162 13 25 112 32 64 128 256), losses := [] }

theorem u11439 : Upper (D 8) (R 8) [66,160,9,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11440 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 25 148 352 352 480 352), lower := (rows 67 162 13 25 148 32 64 128 256), losses := [] }

theorem u11440 : Upper (D 8) (R 8) [66,160,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11441 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 25 208 292 356 420 292), lower := (rows 67 162 13 25 208 32 64 128 256), losses := [] }

theorem u11441 : Upper (D 8) (R 8) [66,160,9,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11442 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 25 276 224 224 224 480), lower := (rows 67 162 13 25 276 32 64 128 256), losses := [] }

theorem u11442 : Upper (D 8) (R 8) [66,160,9,17,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11443 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 25 304 228 228 228 484), lower := (rows 67 162 13 25 304 32 64 128 256), losses := [] }

theorem u11443 : Upper (D 8) (R 8) [66,160,9,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11444 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 25 336 164 228 164 420), lower := (rows 67 162 13 25 336 32 64 128 256), losses := [] }

theorem u11444 : Upper (D 8) (R 8) [66,160,9,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11445 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 25 400 100 100 228 356), lower := (rows 67 162 13 25 400 32 64 128 256), losses := [] }

theorem u11445 : Upper (D 8) (R 8) [66,160,9,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11446 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 28 49 480 480 480 480), lower := (rows 67 162 13 28 49 32 64 128 256), losses := [] }

theorem u11446 : Upper (D 8) (R 8) [66,160,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11447 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 28 81 416 480 416 416), lower := (rows 67 162 13 28 81 32 64 128 256), losses := [] }

theorem u11447 : Upper (D 8) (R 8) [66,160,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11448 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 28 112 417 481 417 417), lower := (rows 67 162 13 28 112 32 64 128 256), losses := [] }

theorem u11448 : Upper (D 8) (R 8) [66,160,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11449 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 28 145 352 352 480 352), lower := (rows 67 162 13 28 145 32 64 128 256), losses := [] }

theorem u11449 : Upper (D 8) (R 8) [66,160,9,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11450 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 13 28 176 353 353 481 353), lower := (rows 67 162 13 28 176 32 64 128 256), losses := [] }

theorem u11450 : Upper (D 8) (R 8) [66,160,9,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11451 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 28 208 289 353 417 289), lower := (rows 67 162 13 28 208 32 64 128 256), losses := [] }

theorem u11451 : Upper (D 8) (R 8) [66,160,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11452 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 28 273 224 224 224 480), lower := (rows 67 162 13 28 273 32 64 128 256), losses := [] }

theorem u11452 : Upper (D 8) (R 8) [66,160,9,20,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11453 : Route 9 := (fun mask => (mask,id))

def c11453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11453 : Upper (D 8) (R 8) [66,160,9,20,288] 13 := by
  apply FastRouting.sound _ _ [66,160,9,20,288] 13 (by decide) (choices 1) [1,64,128] r11453 c11453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3510
  · exact u3511
  · exact u3512

def b11454 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 28 336 161 225 161 417), lower := (rows 67 162 13 28 336 32 64 128 256), losses := [] }

theorem u11454 : Upper (D 8) (R 8) [66,160,9,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11455 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 28 400 97 97 225 353), lower := (rows 67 162 13 28 400 32 64 128 256), losses := [] }

theorem u11455 : Upper (D 8) (R 8) [66,160,9,20,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11456 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 13 41 52 496 464 464 464), lower := (rows 67 162 13 41 52 32 64 128 256), losses := [] }

theorem u11456 : Upper (D 8) (R 8) [66,160,9,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11457 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 41 84 432 496 432 432), lower := (rows 67 162 13 41 84 32 64 128 256), losses := [] }

theorem u11457 : Upper (D 8) (R 8) [66,160,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11458 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 41 112 436 468 404 404), lower := (rows 67 162 13 41 112 32 64 128 256), losses := [] }

theorem u11458 : Upper (D 8) (R 8) [66,160,9,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11459 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 41 148 368 368 496 368), lower := (rows 67 162 13 41 148 32 64 128 256), losses := [] }

theorem u11459 : Upper (D 8) (R 8) [66,160,9,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11459
end Delivery.IrregularNine14.P08
