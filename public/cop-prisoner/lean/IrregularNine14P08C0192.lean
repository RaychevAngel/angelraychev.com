import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0058
import IrregularNine14P08C0059

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11520 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 140 273 112 112 240 368), lower := (rows 67 162 13 140 273 32 64 128 256), losses := [] }

theorem u11520 : Upper (D 8) (R 8) [66,160,9,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11521 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 140 304 113 113 241 369), lower := (rows 67 162 13 140 304 32 64 128 256), losses := [] }

theorem u11521 : Upper (D 8) (R 8) [66,160,9,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11522 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 140 336 49 113 177 305), lower := (rows 67 162 13 140 336 32 64 128 256), losses := [] }

theorem u11522 : Upper (D 8) (R 8) [66,160,9,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11523 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 152 49 356 356 484 356), lower := (rows 67 162 13 152 49 32 64 128 256), losses := [] }

theorem u11523 : Upper (D 8) (R 8) [66,160,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11524 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 152 52 353 353 481 353), lower := (rows 67 162 13 152 52 32 64 128 256), losses := [] }

theorem u11524 : Upper (D 8) (R 8) [66,160,9,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11525 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 152 84 289 353 417 289), lower := (rows 67 162 13 152 84 32 64 128 256), losses := [] }

theorem u11525 : Upper (D 8) (R 8) [66,160,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11526 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 152 112 293 357 421 293), lower := (rows 67 162 13 152 112 32 64 128 256), losses := [] }

theorem u11526 : Upper (D 8) (R 8) [66,160,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11527 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 152 273 100 100 228 356), lower := (rows 67 162 13 152 273 32 64 128 256), losses := [] }

theorem u11527 : Upper (D 8) (R 8) [66,160,9,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11528 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 152 276 97 97 225 353), lower := (rows 67 162 13 152 276 32 64 128 256), losses := [] }

theorem u11528 : Upper (D 8) (R 8) [66,160,9,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11529 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 13 152 304 101 101 229 357), lower := (rows 67 162 13 152 304 32 64 128 256), losses := [] }

theorem u11529 : Upper (D 8) (R 8) [66,160,9,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11530 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 152 336 37 101 165 293), lower := (rows 67 162 13 152 336 32 64 128 256), losses := [] }

theorem u11530 : Upper (D 8) (R 8) [66,160,9,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11531 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 168 49 372 340 468 340), lower := (rows 67 162 13 168 49 32 64 128 256), losses := [] }

theorem u11531 : Upper (D 8) (R 8) [66,160,9,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11532 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 168 52 369 337 465 337), lower := (rows 67 162 13 168 52 32 64 128 256), losses := [] }

theorem u11532 : Upper (D 8) (R 8) [66,160,9,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11533 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 168 84 305 369 433 305), lower := (rows 67 162 13 168 84 32 64 128 256), losses := [] }

theorem u11533 : Upper (D 8) (R 8) [66,160,9,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11534 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 168 112 309 341 405 277), lower := (rows 67 162 13 168 112 32 64 128 256), losses := [] }

theorem u11534 : Upper (D 8) (R 8) [66,160,9,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11535 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 168 273 116 116 244 372), lower := (rows 67 162 13 168 273 32 64 128 256), losses := [] }

theorem u11535 : Upper (D 8) (R 8) [66,160,9,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11536 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 168 276 113 113 241 369), lower := (rows 67 162 13 168 276 32 64 128 256), losses := [] }

theorem u11536 : Upper (D 8) (R 8) [66,160,9,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11537 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 168 304 117 85 213 341), lower := (rows 67 162 13 168 304 32 64 128 256), losses := [] }

theorem u11537 : Upper (D 8) (R 8) [66,160,9,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11538 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 168 336 53 117 181 309), lower := (rows 67 162 13 168 336 32 64 128 256), losses := [] }

theorem u11538 : Upper (D 8) (R 8) [66,160,9,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11539 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 200 49 308 372 436 308), lower := (rows 67 162 13 200 49 32 64 128 256), losses := [] }

theorem u11539 : Upper (D 8) (R 8) [66,160,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11540 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 200 52 305 369 433 305), lower := (rows 67 162 13 200 52 32 64 128 256), losses := [] }

theorem u11540 : Upper (D 8) (R 8) [66,160,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11541 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 200 273 52 116 180 308), lower := (rows 67 162 13 200 273 32 64 128 256), losses := [] }

theorem u11541 : Upper (D 8) (R 8) [66,160,9,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11542 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 200 276 49 113 177 305), lower := (rows 67 162 13 200 276 32 64 128 256), losses := [] }

theorem u11542 : Upper (D 8) (R 8) [66,160,9,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11543 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 200 304 53 117 181 309), lower := (rows 67 162 13 200 304 32 64 128 256), losses := [] }

theorem u11543 : Upper (D 8) (R 8) [66,160,9,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11544 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 265 52 240 240 240 496), lower := (rows 67 162 13 265 52 32 64 128 256), losses := [] }

theorem u11544 : Upper (D 8) (R 8) [66,160,9,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11545 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 265 84 176 240 176 432), lower := (rows 67 162 13 265 84 32 64 128 256), losses := [] }

theorem u11545 : Upper (D 8) (R 8) [66,160,9,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11546 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 265 112 180 244 180 436), lower := (rows 67 162 13 265 112 32 64 128 256), losses := [] }

theorem u11546 : Upper (D 8) (R 8) [66,160,9,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11547 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 265 148 112 112 240 368), lower := (rows 67 162 13 265 148 32 64 128 256), losses := [] }

theorem u11547 : Upper (D 8) (R 8) [66,160,9,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11548 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 265 208 52 116 180 308), lower := (rows 67 162 13 265 208 32 64 128 256), losses := [] }

theorem u11548 : Upper (D 8) (R 8) [66,160,9,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11549 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 268 49 240 240 240 496), lower := (rows 67 162 13 268 49 32 64 128 256), losses := [] }

theorem u11549 : Upper (D 8) (R 8) [66,160,9,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11550 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 268 81 176 240 176 432), lower := (rows 67 162 13 268 81 32 64 128 256), losses := [] }

theorem u11550 : Upper (D 8) (R 8) [66,160,9,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11551 : Route 9 := (fun mask => (mask,id))

def c11551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11551 : Upper (D 8) (R 8) [66,160,9,260,96] 13 := by
  apply FastRouting.sound _ _ [66,160,9,260,96] 13 (by decide) (choices 1) [1,16,128] r11551 c11551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3536
  · exact u3537
  · exact u3538

def b11552 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 13 268 145 112 112 240 368), lower := (rows 67 162 13 268 145 32 64 128 256), losses := [] }

theorem u11552 : Upper (D 8) (R 8) [66,160,9,260,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11553 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 13 268 176 113 113 241 369), lower := (rows 67 162 13 268 176 32 64 128 256), losses := [] }

theorem u11553 : Upper (D 8) (R 8) [66,160,9,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11554 : Route 9 := (fun mask => (mask,id))

def c11554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11554 : Upper (D 8) (R 8) [66,160,9,260,192] 13 := by
  apply FastRouting.sound _ _ [66,160,9,260,192] 13 (by decide) (choices 1) [1,16] r11554 c11554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3539
  · exact u3540

def b11555 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 280 49 228 228 228 484), lower := (rows 67 162 13 280 49 32 64 128 256), losses := [] }

theorem u11555 : Upper (D 8) (R 8) [66,160,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11556 : Route 9 := (fun mask => (mask,id))

def c11556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11556 : Upper (D 8) (R 8) [66,160,9,272,36] 13 := by
  apply FastRouting.sound _ _ [66,160,9,272,36] 13 (by decide) (choices 1) [1,64,128] r11556 c11556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3541
  · exact u3542
  · exact u3543

def b11557 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 280 81 164 228 164 420), lower := (rows 67 162 13 280 81 32 64 128 256), losses := [] }

theorem u11557 : Upper (D 8) (R 8) [66,160,9,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11558 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 280 84 161 225 161 417), lower := (rows 67 162 13 280 84 32 64 128 256), losses := [] }

theorem u11558 : Upper (D 8) (R 8) [66,160,9,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11559 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 280 112 165 229 165 421), lower := (rows 67 162 13 280 112 32 64 128 256), losses := [] }

theorem u11559 : Upper (D 8) (R 8) [66,160,9,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11560 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 13 280 145 100 100 228 356), lower := (rows 67 162 13 280 145 32 64 128 256), losses := [] }

theorem u11560 : Upper (D 8) (R 8) [66,160,9,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11561 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 280 148 97 97 225 353), lower := (rows 67 162 13 280 148 32 64 128 256), losses := [] }

theorem u11561 : Upper (D 8) (R 8) [66,160,9,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11562 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 13 280 176 101 101 229 357), lower := (rows 67 162 13 280 176 32 64 128 256), losses := [] }

theorem u11562 : Upper (D 8) (R 8) [66,160,9,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11563 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 280 208 37 101 165 293), lower := (rows 67 162 13 280 208 32 64 128 256), losses := [] }

theorem u11563 : Upper (D 8) (R 8) [66,160,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11564 : Route 9 := (fun mask => (mask,id))

def c11564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u11564 : Upper (D 8) (R 8) [66,160,9,288,33] 13 := by
  apply FastRouting.sound _ _ [66,160,9,288,33] 13 (by decide) (choices 1) [4,16,64,128] r11564 c11564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3544
  · exact u3545
  · exact u3546
  · exact u3547

def r11565 : Route 9 := (fun mask => (mask,id))

def c11565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u11565 : Upper (D 8) (R 8) [66,160,9,288,36] 13 := by
  apply FastRouting.sound _ _ [66,160,9,288,36] 13 (by decide) (choices 1) [1,16,64,128] r11565 c11565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3548
  · exact u3549
  · exact u3550
  · exact u3551

def b11566 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 296 81 180 244 180 436), lower := (rows 67 162 13 296 81 32 64 128 256), losses := [] }

theorem u11566 : Upper (D 8) (R 8) [66,160,9,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11567 : Route 9 := (fun mask => (mask,id))

def c11567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11567 : Upper (D 8) (R 8) [66,160,9,288,68] 13 := by
  apply FastRouting.sound _ _ [66,160,9,288,68] 13 (by decide) (choices 1) [1,16,128] r11567 c11567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3552
  · exact u3553
  · exact u3554

def r11568 : Route 9 := (fun mask => (mask,id))

def c11568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11568 : Upper (D 8) (R 8) [66,160,9,288,96] 13 := by
  apply FastRouting.sound _ _ [66,160,9,288,96] 13 (by decide) (choices 1) [1,4,16,128] r11568 c11568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3555
  · exact u3556
  · exact u3557
  · exact u3558

def b11569 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 13 296 145 116 116 244 372), lower := (rows 67 162 13 296 145 32 64 128 256), losses := [] }

theorem u11569 : Upper (D 8) (R 8) [66,160,9,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11570 : Route 9 := (fun mask => (mask,id))

def c11570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11570 : Upper (D 8) (R 8) [66,160,9,288,132] 13 := by
  apply FastRouting.sound _ _ [66,160,9,288,132] 13 (by decide) (choices 1) [1,16,64] r11570 c11570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3559
  · exact u3560
  · exact u3561

def b11571 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 13 296 176 117 85 213 341), lower := (rows 67 162 13 296 176 32 64 128 256), losses := [] }

theorem u11571 : Upper (D 8) (R 8) [66,160,9,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11572 : Route 9 := (fun mask => (mask,id))

def c11572 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11572 : Upper (D 8) (R 8) [66,160,9,288,192] 13 := by
  apply FastRouting.sound _ _ [66,160,9,288,192] 13 (by decide) (choices 1) [1,4,16] r11572 c11572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3562
  · exact u3563
  · exact u3564

def b11573 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 328 49 180 244 180 436), lower := (rows 67 162 13 328 49 32 64 128 256), losses := [] }

theorem u11573 : Upper (D 8) (R 8) [66,160,9,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11574 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 328 52 177 241 177 433), lower := (rows 67 162 13 328 52 32 64 128 256), losses := [] }

theorem u11574 : Upper (D 8) (R 8) [66,160,9,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11575 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 328 148 49 113 177 305), lower := (rows 67 162 13 328 148 32 64 128 256), losses := [] }

theorem u11575 : Upper (D 8) (R 8) [66,160,9,320,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11576 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 13 392 49 116 116 244 372), lower := (rows 67 162 13 392 49 32 64 128 256), losses := [] }

theorem u11576 : Upper (D 8) (R 8) [66,160,9,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11577 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 13 392 52 113 113 241 369), lower := (rows 67 162 13 392 52 32 64 128 256), losses := [] }

theorem u11577 : Upper (D 8) (R 8) [66,160,9,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11578 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 13 392 84 49 113 177 305), lower := (rows 67 162 13 392 84 32 64 128 256), losses := [] }

theorem u11578 : Upper (D 8) (R 8) [66,160,9,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11579 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 13 392 112 53 117 181 309), lower := (rows 67 162 13 392 112 32 64 128 256), losses := [] }

theorem u11579 : Upper (D 8) (R 8) [66,160,9,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11579
end Delivery.IrregularNine14.P08
