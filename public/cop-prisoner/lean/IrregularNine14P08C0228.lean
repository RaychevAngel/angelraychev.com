import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0077

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13680 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 74 152 49 113 177 305), lower := (rows 97 7 388 74 152 32 64 128 256), losses := [] }

theorem u13680 : Upper (D 8) (R 8) [96,5,384,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13681 : Route 9 := (fun mask => (mask,id))

def c13681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13681 : Upper (D 8) (R 8) [96,5,384,66,160] 13 := by
  apply FastRouting.sound _ _ [96,5,384,66,160] 13 (by decide) (choices 1) [1,8,16] r13681 c13681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4635
  · exact u4636
  · exact u4637

def r13682 : Route 9 := (fun mask => (mask,id))

def c13682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13682 : Upper (D 8) (R 8) [96,5,384,80,129] 13 := by
  apply FastRouting.sound _ _ [96,5,384,80,129] 13 (by decide) (choices 1) [2,8] r13682 c13682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4638
  · exact u4639

def b13683 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 88 146 41 105 169 297), lower := (rows 97 7 388 88 146 32 64 128 256), losses := [] }

theorem u13683 : Upper (D 8) (R 8) [96,5,384,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13684 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 88 152 35 99 163 291), lower := (rows 97 7 388 88 152 32 64 128 256), losses := [] }

theorem u13684 : Upper (D 8) (R 8) [96,5,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13685 : Route 9 := (fun mask => (mask,id))

def c13685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13685 : Upper (D 8) (R 8) [96,5,384,80,160] 13 := by
  apply FastRouting.sound _ _ [96,5,384,80,160] 13 (by decide) (choices 1) [1,2,8] r13685 c13685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4640
  · exact u4641
  · exact u4642

def b13686 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 104 145 58 122 186 314), lower := (rows 97 7 388 104 145 32 64 128 256), losses := [] }

theorem u13686 : Upper (D 8) (R 8) [96,5,384,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13687 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 104 152 51 115 179 307), lower := (rows 97 7 388 104 152 32 64 128 256), losses := [] }

theorem u13687 : Upper (D 8) (R 8) [96,5,384,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13688 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 388 104 176 59 91 155 283), lower := (rows 97 7 388 104 176 32 64 128 256), losses := [] }

theorem u13688 : Upper (D 8) (R 8) [96,5,384,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13689 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 41 145 480 480 480 480), lower := (rows 97 14 22 41 145 32 64 128 256), losses := [] }

theorem u13689 : Upper (D 8) (R 8) [96,12,18,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13690 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 41 176 481 449 449 449), lower := (rows 97 14 22 41 176 32 64 128 256), losses := [] }

theorem u13690 : Upper (D 8) (R 8) [96,12,18,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13691 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 41 273 224 224 224 480), lower := (rows 97 14 22 41 273 32 64 128 256), losses := [] }

theorem u13691 : Upper (D 8) (R 8) [96,12,18,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13692 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 41 304 225 193 193 449), lower := (rows 97 14 22 41 304 32 64 128 256), losses := [] }

theorem u13692 : Upper (D 8) (R 8) [96,12,18,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13693 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 41 400 225 225 225 481), lower := (rows 97 14 22 41 400 32 64 128 256), losses := [] }

theorem u13693 : Upper (D 8) (R 8) [96,12,18,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13694 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 73 145 416 480 416 416), lower := (rows 97 14 22 73 145 32 64 128 256), losses := [] }

theorem u13694 : Upper (D 8) (R 8) [96,12,18,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13695 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 73 176 417 481 417 417), lower := (rows 97 14 22 73 176 32 64 128 256), losses := [] }

theorem u13695 : Upper (D 8) (R 8) [96,12,18,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13696 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 73 273 160 224 160 416), lower := (rows 97 14 22 73 273 32 64 128 256), losses := [] }

theorem u13696 : Upper (D 8) (R 8) [96,12,18,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13697 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 73 304 161 225 161 417), lower := (rows 97 14 22 73 304 32 64 128 256), losses := [] }

theorem u13697 : Upper (D 8) (R 8) [96,12,18,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13698 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 73 400 161 225 161 417), lower := (rows 97 14 22 73 400 32 64 128 256), losses := [] }

theorem u13698 : Upper (D 8) (R 8) [96,12,18,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13699 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 104 145 417 481 417 417), lower := (rows 97 14 22 104 145 32 64 128 256), losses := [] }

theorem u13699 : Upper (D 8) (R 8) [96,12,18,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13700 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 104 176 417 449 385 385), lower := (rows 97 14 22 104 176 32 64 128 256), losses := [] }

theorem u13700 : Upper (D 8) (R 8) [96,12,18,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13701 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 104 273 161 225 161 417), lower := (rows 97 14 22 104 273 32 64 128 256), losses := [] }

theorem u13701 : Upper (D 8) (R 8) [96,12,18,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13702 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 104 304 161 193 129 385), lower := (rows 97 14 22 104 304 32 64 128 256), losses := [] }

theorem u13702 : Upper (D 8) (R 8) [96,12,18,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13703 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 104 400 161 225 161 417), lower := (rows 97 14 22 104 400 32 64 128 256), losses := [] }

theorem u13703 : Upper (D 8) (R 8) [96,12,18,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13704 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 22 137 145 352 352 480 352), lower := (rows 97 14 22 137 145 32 64 128 256), losses := [] }

theorem u13704 : Upper (D 8) (R 8) [96,12,18,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13705 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 137 176 353 353 481 353), lower := (rows 97 14 22 137 176 32 64 128 256), losses := [] }

theorem u13705 : Upper (D 8) (R 8) [96,12,18,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13706 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 137 208 289 353 417 289), lower := (rows 97 14 22 137 208 32 64 128 256), losses := [] }

theorem u13706 : Upper (D 8) (R 8) [96,12,18,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13707 : Route 9 := (fun mask => (mask,id))

def c13707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13707 : Upper (D 8) (R 8) [96,12,18,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,257] 13 (by decide) (choices 1) [64,128] r13707 c13707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4643
  · exact u4644

def r13708 : Route 9 := (fun mask => (mask,id))

def c13708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13708 : Upper (D 8) (R 8) [96,12,18,129,288] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,288] 13 (by decide) (choices 1) [1,64,128] r13708 c13708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4645
  · exact u4646
  · exact u4647

def b13709 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 137 336 161 225 161 417), lower := (rows 97 14 22 137 336 32 64 128 256), losses := [] }

theorem u13709 : Upper (D 8) (R 8) [96,12,18,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13710 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 137 400 97 97 225 353), lower := (rows 97 14 22 137 400 32 64 128 256), losses := [] }

theorem u13710 : Upper (D 8) (R 8) [96,12,18,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13711 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 22 168 176 353 321 449 321), lower := (rows 97 14 22 168 176 32 64 128 256), losses := [] }

theorem u13711 : Upper (D 8) (R 8) [96,12,18,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13712 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 168 208 289 353 417 289), lower := (rows 97 14 22 168 208 32 64 128 256), losses := [] }

theorem u13712 : Upper (D 8) (R 8) [96,12,18,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13713 : Route 9 := (fun mask => (mask,id))

def c13713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13713 : Upper (D 8) (R 8) [96,12,18,160,257] 13 := by
  apply FastRouting.sound _ _ [96,12,18,160,257] 13 (by decide) (choices 1) [1,64,128] r13713 c13713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4648
  · exact u4649
  · exact u4650

def r13714 : Route 9 := (fun mask => (mask,id))

def c13714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13714 : Upper (D 8) (R 8) [96,12,18,160,288] 13 := by
  apply FastRouting.sound _ _ [96,12,18,160,288] 13 (by decide) (choices 1) [1,64,128] r13714 c13714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4651
  · exact u4652
  · exact u4653

def b13715 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 168 336 161 225 161 417), lower := (rows 97 14 22 168 336 32 64 128 256), losses := [] }

theorem u13715 : Upper (D 8) (R 8) [96,12,18,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13716 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 168 400 97 97 225 353), lower := (rows 97 14 22 168 400 32 64 128 256), losses := [] }

theorem u13716 : Upper (D 8) (R 8) [96,12,18,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13717 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 22 200 273 161 225 161 417), lower := (rows 97 14 22 200 273 32 64 128 256), losses := [] }

theorem u13717 : Upper (D 8) (R 8) [96,12,18,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13718 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 22 200 304 161 225 161 417), lower := (rows 97 14 22 200 304 32 64 128 256), losses := [] }

theorem u13718 : Upper (D 8) (R 8) [96,12,18,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13719 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 22 200 400 33 97 161 289), lower := (rows 97 14 22 200 400 32 64 128 256), losses := [] }

theorem u13719 : Upper (D 8) (R 8) [96,12,18,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13720 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 37 42 145 496 464 464 464), lower := (rows 97 14 37 42 145 32 64 128 256), losses := [] }

theorem u13720 : Upper (D 8) (R 8) [96,12,33,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13721 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 37 42 208 433 465 401 401), lower := (rows 97 14 37 42 208 32 64 128 256), losses := [] }

theorem u13721 : Upper (D 8) (R 8) [96,12,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13722 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 37 42 273 240 208 208 464), lower := (rows 97 14 37 42 273 32 64 128 256), losses := [] }

theorem u13722 : Upper (D 8) (R 8) [96,12,33,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13723 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 37 42 336 177 209 145 401), lower := (rows 97 14 37 42 336 32 64 128 256), losses := [] }

theorem u13723 : Upper (D 8) (R 8) [96,12,33,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13724 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 37 42 400 241 209 209 465), lower := (rows 97 14 37 42 400 32 64 128 256), losses := [] }

theorem u13724 : Upper (D 8) (R 8) [96,12,33,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13725 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 56 145 482 450 450 450), lower := (rows 97 14 37 56 145 32 64 128 256), losses := [] }

theorem u13725 : Upper (D 8) (R 8) [96,12,33,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13726 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 56 146 481 449 449 449), lower := (rows 97 14 37 56 146 32 64 128 256), losses := [] }

theorem u13726 : Upper (D 8) (R 8) [96,12,33,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13727 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 56 208 419 451 387 387), lower := (rows 97 14 37 56 208 32 64 128 256), losses := [] }

theorem u13727 : Upper (D 8) (R 8) [96,12,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13728 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 56 273 226 194 194 450), lower := (rows 97 14 37 56 273 32 64 128 256), losses := [] }

theorem u13728 : Upper (D 8) (R 8) [96,12,33,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13729 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 56 274 225 193 193 449), lower := (rows 97 14 37 56 274 32 64 128 256), losses := [] }

theorem u13729 : Upper (D 8) (R 8) [96,12,33,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13730 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 56 336 163 195 131 387), lower := (rows 97 14 37 56 336 32 64 128 256), losses := [] }

theorem u13730 : Upper (D 8) (R 8) [96,12,33,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13731 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 56 400 227 195 195 451), lower := (rows 97 14 37 56 400 32 64 128 256), losses := [] }

theorem u13731 : Upper (D 8) (R 8) [96,12,33,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13732 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 88 145 418 482 418 418), lower := (rows 97 14 37 88 145 32 64 128 256), losses := [] }

theorem u13732 : Upper (D 8) (R 8) [96,12,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13733 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 88 176 419 451 387 387), lower := (rows 97 14 37 88 176 32 64 128 256), losses := [] }

theorem u13733 : Upper (D 8) (R 8) [96,12,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13734 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 88 273 162 226 162 418), lower := (rows 97 14 37 88 273 32 64 128 256), losses := [] }

theorem u13734 : Upper (D 8) (R 8) [96,12,33,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13735 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 88 304 163 195 131 387), lower := (rows 97 14 37 88 304 32 64 128 256), losses := [] }

theorem u13735 : Upper (D 8) (R 8) [96,12,33,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13736 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 88 400 163 227 163 419), lower := (rows 97 14 37 88 400 32 64 128 256), losses := [] }

theorem u13736 : Upper (D 8) (R 8) [96,12,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13737 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 137 50 496 464 464 464), lower := (rows 97 14 37 137 50 32 64 128 256), losses := [] }

theorem u13737 : Upper (D 8) (R 8) [96,12,33,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13738 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 137 82 432 496 432 432), lower := (rows 97 14 37 137 82 32 64 128 256), losses := [] }

theorem u13738 : Upper (D 8) (R 8) [96,12,33,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13739 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 137 176 370 338 466 338), lower := (rows 97 14 37 137 176 32 64 128 256), losses := [] }

theorem u13739 : Upper (D 8) (R 8) [96,12,33,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13739
end Delivery.IrregularNine14.P08
