import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0031

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8640 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 56 84 417 449 385 385), lower := (rows 35 67 44 56 84 32 64 128 256), losses := [] }

theorem u8640 : Upper (D 8) (R 8) [34,65,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8641 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 56 148 481 449 449 449), lower := (rows 35 67 44 56 148 32 64 128 256), losses := [] }

theorem u8641 : Upper (D 8) (R 8) [34,65,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8642 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 56 208 421 453 389 389), lower := (rows 35 67 44 56 208 32 64 128 256), losses := [] }

theorem u8642 : Upper (D 8) (R 8) [34,65,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8642 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8643 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 56 276 225 193 193 449), lower := (rows 35 67 44 56 276 32 64 128 256), losses := [] }

theorem u8643 : Upper (D 8) (R 8) [34,65,40,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8644 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 56 336 165 197 133 389), lower := (rows 35 67 44 56 336 32 64 128 256), losses := [] }

theorem u8644 : Upper (D 8) (R 8) [34,65,40,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8645 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 56 400 229 197 197 453), lower := (rows 35 67 44 56 400 32 64 128 256), losses := [] }

theorem u8645 : Upper (D 8) (R 8) [34,65,40,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8646 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 148 432 496 432 432), lower := (rows 35 67 44 73 148 32 64 128 256), losses := [] }

theorem u8646 : Upper (D 8) (R 8) [34,65,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8647 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 176 436 468 404 404), lower := (rows 35 67 44 73 176 32 64 128 256), losses := [] }

theorem u8647 : Upper (D 8) (R 8) [34,65,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8648 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 276 176 240 176 432), lower := (rows 35 67 44 73 276 32 64 128 256), losses := [] }

theorem u8648 : Upper (D 8) (R 8) [34,65,40,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8649 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 304 180 212 148 404), lower := (rows 35 67 44 73 304 32 64 128 256), losses := [] }

theorem u8649 : Upper (D 8) (R 8) [34,65,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8650 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 44 73 400 180 244 180 436), lower := (rows 35 67 44 73 400 32 64 128 256), losses := [] }

theorem u8650 : Upper (D 8) (R 8) [34,65,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8651 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 76 176 433 465 401 401), lower := (rows 35 67 44 76 176 32 64 128 256), losses := [] }

theorem u8651 : Upper (D 8) (R 8) [34,65,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8652 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 76 304 177 209 145 401), lower := (rows 35 67 44 76 304 32 64 128 256), losses := [] }

theorem u8652 : Upper (D 8) (R 8) [34,65,40,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8653 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 76 400 177 241 177 433), lower := (rows 35 67 44 76 400 32 64 128 256), losses := [] }

theorem u8653 : Upper (D 8) (R 8) [34,65,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8654 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 88 145 420 484 420 420), lower := (rows 35 67 44 88 145 32 64 128 256), losses := [] }

theorem u8654 : Upper (D 8) (R 8) [34,65,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8655 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 88 148 417 481 417 417), lower := (rows 35 67 44 88 148 32 64 128 256), losses := [] }

theorem u8655 : Upper (D 8) (R 8) [34,65,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8656 : Route 9 := (fun mask => (mask,id))

def c8656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8656 : Upper (D 8) (R 8) [34,65,40,80,160] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,160] 13 (by decide) (choices 1) [1,4,128,256] r8656 c8656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1862
  · exact u1863
  · exact u1864
  · exact u1865

def b8657 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 88 273 164 228 164 420), lower := (rows 35 67 44 88 273 32 64 128 256), losses := [] }

theorem u8657 : Upper (D 8) (R 8) [34,65,40,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8658 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 88 276 161 225 161 417), lower := (rows 35 67 44 88 276 32 64 128 256), losses := [] }

theorem u8658 : Upper (D 8) (R 8) [34,65,40,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8659 : Route 9 := (fun mask => (mask,id))

def c8659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8659 : Upper (D 8) (R 8) [34,65,40,80,288] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,288] 13 (by decide) (choices 1) [1,4,128] r8659 c8659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1866
  · exact u1867
  · exact u1868

def r8660 : Route 9 := (fun mask => (mask,id))

def c8660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8660 : Upper (D 8) (R 8) [34,65,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,384] 13 (by decide) (choices 1) [1,4,128] r8660 c8660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1869
  · exact u1870
  · exact u1871

def b8661 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 104 148 433 465 401 401), lower := (rows 35 67 44 104 148 32 64 128 256), losses := [] }

theorem u8661 : Upper (D 8) (R 8) [34,65,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8662 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 104 276 177 209 145 401), lower := (rows 35 67 44 104 276 32 64 128 256), losses := [] }

theorem u8662 : Upper (D 8) (R 8) [34,65,40,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8663 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 104 400 181 213 149 405), lower := (rows 35 67 44 104 400 32 64 128 256), losses := [] }

theorem u8663 : Upper (D 8) (R 8) [34,65,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8664 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 137 84 432 496 432 432), lower := (rows 35 67 44 137 84 32 64 128 256), losses := [] }

theorem u8664 : Upper (D 8) (R 8) [34,65,40,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8665 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 137 148 368 368 496 368), lower := (rows 35 67 44 137 148 32 64 128 256), losses := [] }

theorem u8665 : Upper (D 8) (R 8) [34,65,40,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8666 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 137 176 372 340 468 340), lower := (rows 35 67 44 137 176 32 64 128 256), losses := [] }

theorem u8666 : Upper (D 8) (R 8) [34,65,40,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8667 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 137 208 308 372 436 308), lower := (rows 35 67 44 137 208 32 64 128 256), losses := [] }

theorem u8667 : Upper (D 8) (R 8) [34,65,40,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8668 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 137 276 240 240 240 496), lower := (rows 35 67 44 137 276 32 64 128 256), losses := [] }

theorem u8668 : Upper (D 8) (R 8) [34,65,40,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8669 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 137 304 244 212 212 468), lower := (rows 35 67 44 137 304 32 64 128 256), losses := [] }

theorem u8669 : Upper (D 8) (R 8) [34,65,40,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8670 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 137 336 180 244 180 436), lower := (rows 35 67 44 137 336 32 64 128 256), losses := [] }

theorem u8670 : Upper (D 8) (R 8) [34,65,40,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8671 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 137 400 116 116 244 372), lower := (rows 35 67 44 137 400 32 64 128 256), losses := [] }

theorem u8671 : Upper (D 8) (R 8) [34,65,40,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8672 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 140 81 432 496 432 432), lower := (rows 35 67 44 140 81 32 64 128 256), losses := [] }

theorem u8672 : Upper (D 8) (R 8) [34,65,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8673 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 140 112 433 465 401 401), lower := (rows 35 67 44 140 112 32 64 128 256), losses := [] }

theorem u8673 : Upper (D 8) (R 8) [34,65,40,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8674 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 145 368 368 496 368), lower := (rows 35 67 44 140 145 32 64 128 256), losses := [] }

theorem u8674 : Upper (D 8) (R 8) [34,65,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8675 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 176 369 337 465 337), lower := (rows 35 67 44 140 176 32 64 128 256), losses := [] }

theorem u8675 : Upper (D 8) (R 8) [34,65,40,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8676 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 140 208 305 369 433 305), lower := (rows 35 67 44 140 208 32 64 128 256), losses := [] }

theorem u8676 : Upper (D 8) (R 8) [34,65,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8677 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 273 240 240 240 496), lower := (rows 35 67 44 140 273 32 64 128 256), losses := [] }

theorem u8677 : Upper (D 8) (R 8) [34,65,40,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8678 : Route 9 := (fun mask => (mask,id))

def c8678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8678 : Upper (D 8) (R 8) [34,65,40,132,288] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,288] 13 (by decide) (choices 1) [1,16,64,128] r8678 c8678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1872
  · exact u1873
  · exact u1874
  · exact u1875

def r8679 : Route 9 := (fun mask => (mask,id))

def c8679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8679 : Upper (D 8) (R 8) [34,65,40,132,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,320] 13 (by decide) (choices 1) [1,16,128] r8679 c8679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1876
  · exact u1877
  · exact u1878

def b8680 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 140 400 113 113 241 369), lower := (rows 35 67 44 140 400 32 64 128 256), losses := [] }

theorem u8680 : Upper (D 8) (R 8) [34,65,40,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8681 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 152 81 420 484 420 420), lower := (rows 35 67 44 152 81 32 64 128 256), losses := [] }

theorem u8681 : Upper (D 8) (R 8) [34,65,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8682 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 152 84 417 481 417 417), lower := (rows 35 67 44 152 84 32 64 128 256), losses := [] }

theorem u8682 : Upper (D 8) (R 8) [34,65,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8683 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 112 421 453 389 389), lower := (rows 35 67 44 152 112 32 64 128 256), losses := [] }

theorem u8683 : Upper (D 8) (R 8) [34,65,40,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8684 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 145 356 356 484 356), lower := (rows 35 67 44 152 145 32 64 128 256), losses := [] }

theorem u8684 : Upper (D 8) (R 8) [34,65,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8685 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 148 353 353 481 353), lower := (rows 35 67 44 152 148 32 64 128 256), losses := [] }

theorem u8685 : Upper (D 8) (R 8) [34,65,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8686 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 152 176 357 325 453 325), lower := (rows 35 67 44 152 176 32 64 128 256), losses := [] }

theorem u8686 : Upper (D 8) (R 8) [34,65,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8687 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 208 293 357 421 293), lower := (rows 35 67 44 152 208 32 64 128 256), losses := [] }

theorem u8687 : Upper (D 8) (R 8) [34,65,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8688 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 152 273 228 228 228 484), lower := (rows 35 67 44 152 273 32 64 128 256), losses := [] }

theorem u8688 : Upper (D 8) (R 8) [34,65,40,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8689 : Route 9 := (fun mask => (mask,id))

def c8689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8689 : Upper (D 8) (R 8) [34,65,40,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,260] 13 (by decide) (choices 1) [1,64,128] r8689 c8689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1879
  · exact u1880
  · exact u1881

def r8690 : Route 9 := (fun mask => (mask,id))

def c8690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8690 : Upper (D 8) (R 8) [34,65,40,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,288] 13 (by decide) (choices 1) [1,4,64,128] r8690 c8690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1882
  · exact u1883
  · exact u1884
  · exact u1885

def r8691 : Route 9 := (fun mask => (mask,id))

def c8691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8691 : Upper (D 8) (R 8) [34,65,40,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,320] 13 (by decide) (choices 1) [1,4,128] r8691 c8691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1886
  · exact u1887
  · exact u1888

def b8692 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 400 101 101 229 357), lower := (rows 35 67 44 152 400 32 64 128 256), losses := [] }

theorem u8692 : Upper (D 8) (R 8) [34,65,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8693 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 168 84 433 465 401 401), lower := (rows 35 67 44 168 84 32 64 128 256), losses := [] }

theorem u8693 : Upper (D 8) (R 8) [34,65,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8694 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 168 148 369 337 465 337), lower := (rows 35 67 44 168 148 32 64 128 256), losses := [] }

theorem u8694 : Upper (D 8) (R 8) [34,65,40,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8695 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 168 208 309 341 405 277), lower := (rows 35 67 44 168 208 32 64 128 256), losses := [] }

theorem u8695 : Upper (D 8) (R 8) [34,65,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8696 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 168 276 241 209 209 465), lower := (rows 35 67 44 168 276 32 64 128 256), losses := [] }

theorem u8696 : Upper (D 8) (R 8) [34,65,40,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8697 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 168 336 181 213 149 405), lower := (rows 35 67 44 168 336 32 64 128 256), losses := [] }

theorem u8697 : Upper (D 8) (R 8) [34,65,40,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8698 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 168 400 117 85 213 341), lower := (rows 35 67 44 168 400 32 64 128 256), losses := [] }

theorem u8698 : Upper (D 8) (R 8) [34,65,40,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8699 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 200 145 308 372 436 308), lower := (rows 35 67 44 200 145 32 64 128 256), losses := [] }

theorem u8699 : Upper (D 8) (R 8) [34,65,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8699
end Delivery.IrregularNine14.P08
