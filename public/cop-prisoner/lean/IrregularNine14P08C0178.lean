import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0050
import IrregularNine14P08C0051

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r10680 : Route 9 := (fun mask => (mask,id))

def c10680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10680 : Upper (D 8) (R 8) [66,36,9,160,384] 13 := by
  apply FastRouting.sound _ _ [66,36,9,160,384] 13 (by decide) (choices 1) [1,16,64] r10680 c10680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3042
  · exact u3043
  · exact u3044

def b10681 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 13 280 49 224 224 224 480), lower := (rows 67 38 13 280 49 32 64 128 256), losses := [] }

theorem u10681 : Upper (D 8) (R 8) [66,36,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10682 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 280 81 160 224 160 416), lower := (rows 67 38 13 280 81 32 64 128 256), losses := [] }

theorem u10682 : Upper (D 8) (R 8) [66,36,9,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10683 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 280 112 161 225 161 417), lower := (rows 67 38 13 280 112 32 64 128 256), losses := [] }

theorem u10683 : Upper (D 8) (R 8) [66,36,9,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10684 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 13 280 145 224 224 224 480), lower := (rows 67 38 13 280 145 32 64 128 256), losses := [] }

theorem u10684 : Upper (D 8) (R 8) [66,36,9,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10685 : Route 9 := (fun mask => (mask,id))

def c10685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10685 : Upper (D 8) (R 8) [66,36,9,272,160] 13 := by
  apply FastRouting.sound _ _ [66,36,9,272,160] 13 (by decide) (choices 1) [1,64,128] r10685 c10685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3045
  · exact u3046
  · exact u3047

def b10686 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 280 208 161 225 161 417), lower := (rows 67 38 13 280 208 32 64 128 256), losses := [] }

theorem u10686 : Upper (D 8) (R 8) [66,36,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10687 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 296 49 240 208 208 464), lower := (rows 67 38 13 296 49 32 64 128 256), losses := [] }

theorem u10687 : Upper (D 8) (R 8) [66,36,9,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10688 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 296 81 176 240 176 432), lower := (rows 67 38 13 296 81 32 64 128 256), losses := [] }

theorem u10688 : Upper (D 8) (R 8) [66,36,9,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10689 : Route 9 := (fun mask => (mask,id))

def c10689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10689 : Upper (D 8) (R 8) [66,36,9,288,96] 13 := by
  apply FastRouting.sound _ _ [66,36,9,288,96] 13 (by decide) (choices 1) [1,16,128] r10689 c10689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3048
  · exact u3049
  · exact u3050

def b10690 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 296 145 240 240 240 496), lower := (rows 67 38 13 296 145 32 64 128 256), losses := [] }

theorem u10690 : Upper (D 8) (R 8) [66,36,9,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10691 : Route 9 := (fun mask => (mask,id))

def c10691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10691 : Upper (D 8) (R 8) [66,36,9,288,160] 13 := by
  apply FastRouting.sound _ _ [66,36,9,288,160] 13 (by decide) (choices 1) [1,16,64,128] r10691 c10691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3051
  · exact u3052
  · exact u3053
  · exact u3054

def r10692 : Route 9 := (fun mask => (mask,id))

def c10692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10692 : Upper (D 8) (R 8) [66,36,9,288,192] 13 := by
  apply FastRouting.sound _ _ [66,36,9,288,192] 13 (by decide) (choices 1) [1,16,128] r10692 c10692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3055
  · exact u3056
  · exact u3057

def b10693 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 392 49 240 240 240 496), lower := (rows 67 38 13 392 49 32 64 128 256), losses := [] }

theorem u10693 : Upper (D 8) (R 8) [66,36,9,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10694 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 392 81 176 240 176 432), lower := (rows 67 38 13 392 81 32 64 128 256), losses := [] }

theorem u10694 : Upper (D 8) (R 8) [66,36,9,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10695 : Route 9 := (fun mask => (mask,id))

def c10695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10695 : Upper (D 8) (R 8) [66,36,9,384,96] 13 := by
  apply FastRouting.sound _ _ [66,36,9,384,96] 13 (by decide) (choices 1) [1,16,128] r10695 c10695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3058
  · exact u3059
  · exact u3060

def b10696 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 392 145 112 112 240 368), lower := (rows 67 38 13 392 145 32 64 128 256), losses := [] }

theorem u10696 : Upper (D 8) (R 8) [66,36,9,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10697 : Route 9 := (fun mask => (mask,id))

def c10697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10697 : Upper (D 8) (R 8) [66,36,9,384,160] 13 := by
  apply FastRouting.sound _ _ [66,36,9,384,160] 13 (by decide) (choices 1) [1,16,64] r10697 c10697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3061
  · exact u3062
  · exact u3063

def r10698 : Route 9 := (fun mask => (mask,id))

def c10698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10698 : Upper (D 8) (R 8) [66,36,9,384,192] 13 := by
  apply FastRouting.sound _ _ [66,36,9,384,192] 13 (by decide) (choices 1) [1,16] r10698 c10698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3064
  · exact u3065

def b10699 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 22, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 28 41 49 480 448 448 448), lower := (rows 67 38 28 41 49 32 64 128 256), losses := [] }

theorem u10699 : Upper (D 8) (R 8) [66,36,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10700 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 28 41 81 416 480 416 416), lower := (rows 67 38 28 41 81 32 64 128 256), losses := [] }

theorem u10700 : Upper (D 8) (R 8) [66,36,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10701 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 41 112 417 449 385 385), lower := (rows 67 38 28 41 112 32 64 128 256), losses := [] }

theorem u10701 : Upper (D 8) (R 8) [66,36,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10702 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 28 41 145 480 480 480 480), lower := (rows 67 38 28 41 145 32 64 128 256), losses := [] }

theorem u10702 : Upper (D 8) (R 8) [66,36,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10703 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 67 38 28 41 176 481 449 449 449), lower := (rows 67 38 28 41 176 32 64 128 256), losses := [] }

theorem u10703 : Upper (D 8) (R 8) [66,36,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10704 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 28 41 208 417 481 417 417), lower := (rows 67 38 28 41 208 32 64 128 256), losses := [] }

theorem u10704 : Upper (D 8) (R 8) [66,36,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10705 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 28 41 273 224 224 224 480), lower := (rows 67 38 28 41 273 32 64 128 256), losses := [] }

theorem u10705 : Upper (D 8) (R 8) [66,36,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10706 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 193, targets := 32 }], pairs := [(0,5)], upper := (rows 67 38 28 41 304 225 193 193 449), lower := (rows 67 38 28 41 304 32 64 128 256), losses := [] }

theorem u10706 : Upper (D 8) (R 8) [66,36,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10707 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 28 41 336 161 225 161 417), lower := (rows 67 38 28 41 336 32 64 128 256), losses := [] }

theorem u10707 : Upper (D 8) (R 8) [66,36,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10708 : Route 9 := (fun mask => (mask,id))

def c10708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10708 : Upper (D 8) (R 8) [66,36,24,33,384] 13 := by
  apply FastRouting.sound _ _ [66,36,24,33,384] 13 (by decide) (choices 1) [1,64,128] r10708 c10708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3066
  · exact u3067
  · exact u3068

def b10709 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 28 73 145 416 480 416 416), lower := (rows 67 38 28 73 145 32 64 128 256), losses := [] }

theorem u10709 : Upper (D 8) (R 8) [66,36,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10710 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 28 73 176 417 481 417 417), lower := (rows 67 38 28 73 176 32 64 128 256), losses := [] }

theorem u10710 : Upper (D 8) (R 8) [66,36,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10711 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 28 73 273 160 224 160 416), lower := (rows 67 38 28 73 273 32 64 128 256), losses := [] }

theorem u10711 : Upper (D 8) (R 8) [66,36,24,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10712 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 28 73 304 161 225 161 417), lower := (rows 67 38 28 73 304 32 64 128 256), losses := [] }

theorem u10712 : Upper (D 8) (R 8) [66,36,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10713 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 28 73 400 161 225 161 417), lower := (rows 67 38 28 73 400 32 64 128 256), losses := [] }

theorem u10713 : Upper (D 8) (R 8) [66,36,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10714 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 104 145 417 481 417 417), lower := (rows 67 38 28 104 145 32 64 128 256), losses := [] }

theorem u10714 : Upper (D 8) (R 8) [66,36,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10715 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 104 176 417 449 385 385), lower := (rows 67 38 28 104 176 32 64 128 256), losses := [] }

theorem u10715 : Upper (D 8) (R 8) [66,36,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10716 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 104 273 161 225 161 417), lower := (rows 67 38 28 104 273 32 64 128 256), losses := [] }

theorem u10716 : Upper (D 8) (R 8) [66,36,24,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10717 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 104 304 161 193 129 385), lower := (rows 67 38 28 104 304 32 64 128 256), losses := [] }

theorem u10717 : Upper (D 8) (R 8) [66,36,24,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10718 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 104 400 161 225 161 417), lower := (rows 67 38 28 104 400 32 64 128 256), losses := [] }

theorem u10718 : Upper (D 8) (R 8) [66,36,24,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10719 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 67 38 28 137 145 352 352 480 352), lower := (rows 67 38 28 137 145 32 64 128 256), losses := [] }

theorem u10719 : Upper (D 8) (R 8) [66,36,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10720 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 137 176 353 353 481 353), lower := (rows 67 38 28 137 176 32 64 128 256), losses := [] }

theorem u10720 : Upper (D 8) (R 8) [66,36,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10721 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 137 208 289 353 417 289), lower := (rows 67 38 28 137 208 32 64 128 256), losses := [] }

theorem u10721 : Upper (D 8) (R 8) [66,36,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10722 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 28 137 273 224 224 224 480), lower := (rows 67 38 28 137 273 32 64 128 256), losses := [] }

theorem u10722 : Upper (D 8) (R 8) [66,36,24,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10723 : Route 9 := (fun mask => (mask,id))

def c10723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10723 : Upper (D 8) (R 8) [66,36,24,129,288] 13 := by
  apply FastRouting.sound _ _ [66,36,24,129,288] 13 (by decide) (choices 1) [1,64,128] r10723 c10723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3069
  · exact u3070
  · exact u3071

def b10724 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 28 137 336 161 225 161 417), lower := (rows 67 38 28 137 336 32 64 128 256), losses := [] }

theorem u10724 : Upper (D 8) (R 8) [66,36,24,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10725 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 137 400 97 97 225 353), lower := (rows 67 38 28 137 400 32 64 128 256), losses := [] }

theorem u10725 : Upper (D 8) (R 8) [66,36,24,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10726 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 28 168 176 353 321 449 321), lower := (rows 67 38 28 168 176 32 64 128 256), losses := [] }

theorem u10726 : Upper (D 8) (R 8) [66,36,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10727 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 168 208 289 353 417 289), lower := (rows 67 38 28 168 208 32 64 128 256), losses := [] }

theorem u10727 : Upper (D 8) (R 8) [66,36,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10728 : Route 9 := (fun mask => (mask,id))

def c10728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10728 : Upper (D 8) (R 8) [66,36,24,160,257] 13 := by
  apply FastRouting.sound _ _ [66,36,24,160,257] 13 (by decide) (choices 1) [1,64,128] r10728 c10728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3072
  · exact u3073
  · exact u3074

def b10729 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 193, targets := 32 }], pairs := [(0,5)], upper := (rows 67 38 28 168 304 225 193 193 449), lower := (rows 67 38 28 168 304 32 64 128 256), losses := [] }

theorem u10729 : Upper (D 8) (R 8) [66,36,24,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10730 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 28 168 336 161 225 161 417), lower := (rows 67 38 28 168 336 32 64 128 256), losses := [] }

theorem u10730 : Upper (D 8) (R 8) [66,36,24,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10731 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 168 400 97 97 225 353), lower := (rows 67 38 28 168 400 32 64 128 256), losses := [] }

theorem u10731 : Upper (D 8) (R 8) [66,36,24,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10732 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 200 273 161 225 161 417), lower := (rows 67 38 28 200 273 32 64 128 256), losses := [] }

theorem u10732 : Upper (D 8) (R 8) [66,36,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10733 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 28 200 304 161 225 161 417), lower := (rows 67 38 28 200 304 32 64 128 256), losses := [] }

theorem u10733 : Upper (D 8) (R 8) [66,36,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10734 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 200 400 33 97 161 289), lower := (rows 67 38 28 200 400 32 64 128 256), losses := [] }

theorem u10734 : Upper (D 8) (R 8) [66,36,24,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10735 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 354, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 133 25 56 480 480 480 480), lower := (rows 67 38 133 25 56 32 64 128 256), losses := [] }

theorem u10735 : Upper (D 8) (R 8) [66,36,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10736 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 133 25 88 416 480 416 416), lower := (rows 67 38 133 25 88 32 64 128 256), losses := [] }

theorem u10736 : Upper (D 8) (R 8) [66,36,129,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10737 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 25 112 424 488 424 424), lower := (rows 67 38 133 25 112 32 64 128 256), losses := [] }

theorem u10737 : Upper (D 8) (R 8) [66,36,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10738 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 133 25 152 352 352 480 352), lower := (rows 67 38 133 25 152 32 64 128 256), losses := [] }

theorem u10738 : Upper (D 8) (R 8) [66,36,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10739 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 25 176 360 360 488 360), lower := (rows 67 38 133 25 176 32 64 128 256), losses := [] }

theorem u10739 : Upper (D 8) (R 8) [66,36,129,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10739
end Delivery.IrregularNine14.P08
