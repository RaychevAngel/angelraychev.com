import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0061
import IrregularNine14P08C0062

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11700 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 168 280 117 85 213 341), lower := (rows 67 162 37 168 280 32 64 128 256), losses := [] }

theorem u11700 : Upper (D 8) (R 8) [66,160,33,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11701 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 168 336 61 93 157 285), lower := (rows 67 162 37 168 336 32 64 128 256), losses := [] }

theorem u11701 : Upper (D 8) (R 8) [66,160,33,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11702 : Route 9 := (fun mask => (mask,id))

def c11702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11702 : Upper (D 8) (R 8) [66,160,33,192,257] 13 := by
  apply FastRouting.sound _ _ [66,160,33,192,257] 13 (by decide) (choices 1) [4,8,16] r11702 c11702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3714
  · exact u3715
  · exact u3716

def r11703 : Route 9 := (fun mask => (mask,id))

def c11703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11703 : Upper (D 8) (R 8) [66,160,33,192,260] 13 := by
  apply FastRouting.sound _ _ [66,160,33,192,260] 13 (by decide) (choices 1) [1,8,16] r11703 c11703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3717
  · exact u3718
  · exact u3719

def r11704 : Route 9 := (fun mask => (mask,id))

def c11704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11704 : Upper (D 8) (R 8) [66,160,33,192,264] 13 := by
  apply FastRouting.sound _ _ [66,160,33,192,264] 13 (by decide) (choices 1) [1,4,16] r11704 c11704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3720
  · exact u3721
  · exact u3722

def r11705 : Route 9 := (fun mask => (mask,id))

def c11705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11705 : Upper (D 8) (R 8) [66,160,33,192,288] 13 := by
  apply FastRouting.sound _ _ [66,160,33,192,288] 13 (by decide) (choices 1) [1,4,8,16] r11705 c11705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3723
  · exact u3724
  · exact u3725
  · exact u3726

def b11706 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 44 208 305 337 401 273), lower := (rows 67 162 44 44 208 32 64 128 256), losses := [] }

theorem u11706 : Upper (D 8) (R 8) [66,160,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11707 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 44 273 241 209 209 465), lower := (rows 67 162 44 44 273 32 64 128 256), losses := [] }

theorem u11707 : Upper (D 8) (R 8) [66,160,40,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11708 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 44 336 177 209 145 401), lower := (rows 67 162 44 44 336 32 64 128 256), losses := [] }

theorem u11708 : Upper (D 8) (R 8) [66,160,40,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11709 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 44 400 113 81 209 337), lower := (rows 67 162 44 44 400 32 64 128 256), losses := [] }

theorem u11709 : Upper (D 8) (R 8) [66,160,40,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11710 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 56 84 417 449 385 385), lower := (rows 67 162 44 56 84 32 64 128 256), losses := [] }

theorem u11710 : Upper (D 8) (R 8) [66,160,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11711 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 28, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 56 148 353 321 449 321), lower := (rows 67 162 44 56 148 32 64 128 256), losses := [] }

theorem u11711 : Upper (D 8) (R 8) [66,160,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11712 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 56 208 293 325 389 261), lower := (rows 67 162 44 56 208 32 64 128 256), losses := [] }

theorem u11712 : Upper (D 8) (R 8) [66,160,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11713 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 56 273 229 197 197 453), lower := (rows 67 162 44 56 273 32 64 128 256), losses := [] }

theorem u11713 : Upper (D 8) (R 8) [66,160,40,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11714 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 56 276 225 193 193 449), lower := (rows 67 162 44 56 276 32 64 128 256), losses := [] }

theorem u11714 : Upper (D 8) (R 8) [66,160,40,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11715 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 56 336 165 197 133 389), lower := (rows 67 162 44 56 336 32 64 128 256), losses := [] }

theorem u11715 : Upper (D 8) (R 8) [66,160,40,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11716 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 56 400 101 69 197 325), lower := (rows 67 162 44 56 400 32 64 128 256), losses := [] }

theorem u11716 : Upper (D 8) (R 8) [66,160,40,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11717 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 73 148 305 369 433 305), lower := (rows 67 162 44 73 148 32 64 128 256), losses := [] }

theorem u11717 : Upper (D 8) (R 8) [66,160,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11718 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 73 273 180 244 180 436), lower := (rows 67 162 44 73 273 32 64 128 256), losses := [] }

theorem u11718 : Upper (D 8) (R 8) [66,160,40,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11719 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 73 276 177 241 177 433), lower := (rows 67 162 44 73 276 32 64 128 256), losses := [] }

theorem u11719 : Upper (D 8) (R 8) [66,160,40,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11720 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 73 304 181 213 149 405), lower := (rows 67 162 44 73 304 32 64 128 256), losses := [] }

theorem u11720 : Upper (D 8) (R 8) [66,160,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11721 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 73 400 53 117 181 309), lower := (rows 67 162 44 73 400 32 64 128 256), losses := [] }

theorem u11721 : Upper (D 8) (R 8) [66,160,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11722 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 76 273 177 241 177 433), lower := (rows 67 162 44 76 273 32 64 128 256), losses := [] }

theorem u11722 : Upper (D 8) (R 8) [66,160,40,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11723 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 76 304 177 209 145 401), lower := (rows 67 162 44 76 304 32 64 128 256), losses := [] }

theorem u11723 : Upper (D 8) (R 8) [66,160,40,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11724 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 76 400 49 113 177 305), lower := (rows 67 162 44 76 400 32 64 128 256), losses := [] }

theorem u11724 : Upper (D 8) (R 8) [66,160,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11725 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 88 145 293 357 421 293), lower := (rows 67 162 44 88 145 32 64 128 256), losses := [] }

theorem u11725 : Upper (D 8) (R 8) [66,160,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11726 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 88 148 289 353 417 289), lower := (rows 67 162 44 88 148 32 64 128 256), losses := [] }

theorem u11726 : Upper (D 8) (R 8) [66,160,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11727 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 44 88 176 293 325 389 261), lower := (rows 67 162 44 88 176 32 64 128 256), losses := [] }

theorem u11727 : Upper (D 8) (R 8) [66,160,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11728 : Route 9 := (fun mask => (mask,id))

def c11728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11728 : Upper (D 8) (R 8) [66,160,40,80,257] 13 := by
  apply FastRouting.sound _ _ [66,160,40,80,257] 13 (by decide) (choices 1) [1,4,128] r11728 c11728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3727
  · exact u3728
  · exact u3729

def b11729 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 88 276 161 225 161 417), lower := (rows 67 162 44 88 276 32 64 128 256), losses := [] }

theorem u11729 : Upper (D 8) (R 8) [66,160,40,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11730 : Route 9 := (fun mask => (mask,id))

def c11730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11730 : Upper (D 8) (R 8) [66,160,40,80,288] 13 := by
  apply FastRouting.sound _ _ [66,160,40,80,288] 13 (by decide) (choices 1) [1,4,128] r11730 c11730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3730
  · exact u3731
  · exact u3732

def r11731 : Route 9 := (fun mask => (mask,id))

def c11731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11731 : Upper (D 8) (R 8) [66,160,40,80,384] 13 := by
  apply FastRouting.sound _ _ [66,160,40,80,384] 13 (by decide) (choices 1) [1,4] r11731 c11731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3733
  · exact u3734

def b11732 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 104 148 305 337 401 273), lower := (rows 67 162 44 104 148 32 64 128 256), losses := [] }

theorem u11732 : Upper (D 8) (R 8) [66,160,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11733 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 104 273 181 213 149 405), lower := (rows 67 162 44 104 273 32 64 128 256), losses := [] }

theorem u11733 : Upper (D 8) (R 8) [66,160,40,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11734 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 104 276 177 209 145 401), lower := (rows 67 162 44 104 276 32 64 128 256), losses := [] }

theorem u11734 : Upper (D 8) (R 8) [66,160,40,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11735 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 104 400 53 85 149 277), lower := (rows 67 162 44 104 400 32 64 128 256), losses := [] }

theorem u11735 : Upper (D 8) (R 8) [66,160,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11736 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 137 84 305 369 433 305), lower := (rows 67 162 44 137 84 32 64 128 256), losses := [] }

theorem u11736 : Upper (D 8) (R 8) [66,160,40,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11737 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 137 112 309 341 405 277), lower := (rows 67 162 44 137 112 32 64 128 256), losses := [] }

theorem u11737 : Upper (D 8) (R 8) [66,160,40,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11738 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 137 273 116 116 244 372), lower := (rows 67 162 44 137 273 32 64 128 256), losses := [] }

theorem u11738 : Upper (D 8) (R 8) [66,160,40,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11739 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 137 276 113 113 241 369), lower := (rows 67 162 44 137 276 32 64 128 256), losses := [] }

theorem u11739 : Upper (D 8) (R 8) [66,160,40,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11740 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 137 304 117 85 213 341), lower := (rows 67 162 44 137 304 32 64 128 256), losses := [] }

theorem u11740 : Upper (D 8) (R 8) [66,160,40,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11741 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 44 137 336 53 117 181 309), lower := (rows 67 162 44 137 336 32 64 128 256), losses := [] }

theorem u11741 : Upper (D 8) (R 8) [66,160,40,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11742 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 140 112 305 337 401 273), lower := (rows 67 162 44 140 112 32 64 128 256), losses := [] }

theorem u11742 : Upper (D 8) (R 8) [66,160,40,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11743 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 140 273 113 113 241 369), lower := (rows 67 162 44 140 273 32 64 128 256), losses := [] }

theorem u11743 : Upper (D 8) (R 8) [66,160,40,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11744 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 140 304 113 81 209 337), lower := (rows 67 162 44 140 304 32 64 128 256), losses := [] }

theorem u11744 : Upper (D 8) (R 8) [66,160,40,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11745 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 140 336 49 113 177 305), lower := (rows 67 162 44 140 336 32 64 128 256), losses := [] }

theorem u11745 : Upper (D 8) (R 8) [66,160,40,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11746 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 152 81 293 357 421 293), lower := (rows 67 162 44 152 81 32 64 128 256), losses := [] }

theorem u11746 : Upper (D 8) (R 8) [66,160,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11747 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 44 152 84 289 353 417 289), lower := (rows 67 162 44 152 84 32 64 128 256), losses := [] }

theorem u11747 : Upper (D 8) (R 8) [66,160,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11748 : Route 9 := (fun mask => (mask,id))

def c11748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11748 : Upper (D 8) (R 8) [66,160,40,144,96] 13 := by
  apply FastRouting.sound _ _ [66,160,40,144,96] 13 (by decide) (choices 1) [1,4,256] r11748 c11748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3735
  · exact u3736
  · exact u3737

def r11749 : Route 9 := (fun mask => (mask,id))

def c11749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11749 : Upper (D 8) (R 8) [66,160,40,144,257] 13 := by
  apply FastRouting.sound _ _ [66,160,40,144,257] 13 (by decide) (choices 1) [1,4,64] r11749 c11749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3738
  · exact u3739
  · exact u3740

def b11750 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 152 276 97 97 225 353), lower := (rows 67 162 44 152 276 32 64 128 256), losses := [] }

theorem u11750 : Upper (D 8) (R 8) [66,160,40,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11751 : Route 9 := (fun mask => (mask,id))

def c11751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11751 : Upper (D 8) (R 8) [66,160,40,144,288] 13 := by
  apply FastRouting.sound _ _ [66,160,40,144,288] 13 (by decide) (choices 1) [1,4,64] r11751 c11751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3741
  · exact u3742
  · exact u3743

def r11752 : Route 9 := (fun mask => (mask,id))

def c11752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11752 : Upper (D 8) (R 8) [66,160,40,144,320] 13 := by
  apply FastRouting.sound _ _ [66,160,40,144,320] 13 (by decide) (choices 1) [1,4] r11752 c11752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3744
  · exact u3745

def b11753 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 168 84 305 337 401 273), lower := (rows 67 162 44 168 84 32 64 128 256), losses := [] }

theorem u11753 : Upper (D 8) (R 8) [66,160,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11754 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 168 273 117 85 213 341), lower := (rows 67 162 44 168 273 32 64 128 256), losses := [] }

theorem u11754 : Upper (D 8) (R 8) [66,160,40,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11755 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 168 276 113 81 209 337), lower := (rows 67 162 44 168 276 32 64 128 256), losses := [] }

theorem u11755 : Upper (D 8) (R 8) [66,160,40,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11756 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 44 168 336 53 85 149 277), lower := (rows 67 162 44 168 336 32 64 128 256), losses := [] }

theorem u11756 : Upper (D 8) (R 8) [66,160,40,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11757 : Route 9 := (fun mask => (mask,id))

def c11757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11757 : Upper (D 8) (R 8) [66,160,40,192,257] 13 := by
  apply FastRouting.sound _ _ [66,160,40,192,257] 13 (by decide) (choices 1) [1,4,16] r11757 c11757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3746
  · exact u3747
  · exact u3748

def r11758 : Route 9 := (fun mask => (mask,id))

def c11758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11758 : Upper (D 8) (R 8) [66,160,40,192,260] 13 := by
  apply FastRouting.sound _ _ [66,160,40,192,260] 13 (by decide) (choices 1) [1,16] r11758 c11758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3749
  · exact u3750

def r11759 : Route 9 := (fun mask => (mask,id))

def c11759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11759 : Upper (D 8) (R 8) [66,160,40,192,288] 13 := by
  apply FastRouting.sound _ _ [66,160,40,192,288] 13 (by decide) (choices 1) [1,4,16] r11759 c11759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3751
  · exact u3752
  · exact u3753

#print axioms u11759
end Delivery.IrregularNine14.P08
