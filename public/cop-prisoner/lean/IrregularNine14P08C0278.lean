import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0100
import IrregularNine14P08C0101

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16680 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 41 112 184 248 184 440), lower := (rows 259 70 133 41 112 32 64 128 256), losses := [] }

theorem u16680 : Upper (D 8) (R 8) [258,68,129,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16681 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 41 152 112 112 240 368), lower := (rows 259 70 133 41 152 32 64 128 256), losses := [] }

theorem u16681 : Upper (D 8) (R 8) [258,68,129,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16682 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 41 176 120 120 248 376), lower := (rows 259 70 133 41 176 32 64 128 256), losses := [] }

theorem u16682 : Upper (D 8) (R 8) [258,68,129,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16683 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 41 208 56 120 184 312), lower := (rows 259 70 133 41 208 32 64 128 256), losses := [] }

theorem u16683 : Upper (D 8) (R 8) [258,68,129,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16684 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 133 56 56 225 225 225 481), lower := (rows 259 70 133 56 56 32 64 128 256), losses := [] }

theorem u16684 : Upper (D 8) (R 8) [258,68,129,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16685 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 133 56 81 168 232 168 424), lower := (rows 259 70 133 56 81 32 64 128 256), losses := [] }

theorem u16685 : Upper (D 8) (R 8) [258,68,129,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16686 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 133 56 88 161 225 161 417), lower := (rows 259 70 133 56 88 32 64 128 256), losses := [] }

theorem u16686 : Upper (D 8) (R 8) [258,68,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16687 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 133 56 112 169 233 169 425), lower := (rows 259 70 133 56 112 32 64 128 256), losses := [] }

theorem u16687 : Upper (D 8) (R 8) [258,68,129,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16688 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 70 133 56 145 104 104 232 360), lower := (rows 259 70 133 56 145 32 64 128 256), losses := [] }

theorem u16688 : Upper (D 8) (R 8) [258,68,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16689 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 133 56 152 97 97 225 353), lower := (rows 259 70 133 56 152 32 64 128 256), losses := [] }

theorem u16689 : Upper (D 8) (R 8) [258,68,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16690 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 133 56 176 105 105 233 361), lower := (rows 259 70 133 56 176 32 64 128 256), losses := [] }

theorem u16690 : Upper (D 8) (R 8) [258,68,129,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16691 : Route 9 := (fun mask => (mask,id))

def c16691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16691 : Upper (D 8) (R 8) [258,68,129,48,192] 13 := by
  apply FastRouting.sound _ _ [258,68,129,48,192] 13 (by decide) (choices 1) [1,8] r16691 c16691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6033
  · exact u6034

def b16692 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 133 73 152 48 112 176 304), lower := (rows 259 70 133 73 152 32 64 128 256), losses := [] }

theorem u16692 : Upper (D 8) (R 8) [258,68,129,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16693 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 133 73 176 56 120 184 312), lower := (rows 259 70 133 73 176 32 64 128 256), losses := [] }

theorem u16693 : Upper (D 8) (R 8) [258,68,129,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16694 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 70 133 88 145 40 104 168 296), lower := (rows 259 70 133 88 145 32 64 128 256), losses := [] }

theorem u16694 : Upper (D 8) (R 8) [258,68,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16695 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 133 88 152 33 97 161 289), lower := (rows 259 70 133 88 152 32 64 128 256), losses := [] }

theorem u16695 : Upper (D 8) (R 8) [258,68,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16696 : Route 9 := (fun mask => (mask,id))

def c16696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16696 : Upper (D 8) (R 8) [258,68,129,80,160] 13 := by
  apply FastRouting.sound _ _ [258,68,129,80,160] 13 (by decide) (choices 1) [1,8] r16696 c16696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6035
  · exact u6036

def b16697 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 70 133 104 145 56 120 184 312), lower := (rows 259 70 133 104 145 32 64 128 256), losses := [] }

theorem u16697 : Upper (D 8) (R 8) [258,68,129,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16698 : Route 9 := (fun mask => (mask,id))

def c16698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16698 : Upper (D 8) (R 8) [258,68,129,96,136] 13 := by
  apply FastRouting.sound _ _ [258,68,129,96,136] 13 (by decide) (choices 1) [1,16] r16698 c16698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6037
  · exact u6038

def r16699 : Route 9 := (fun mask => (mask,id))

def c16699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16699 : Upper (D 8) (R 8) [258,68,129,96,160] 13 := by
  apply FastRouting.sound _ _ [258,68,129,96,160] 13 (by decide) (choices 1) [1,8,16] r16699 c16699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6039
  · exact u6040
  · exact u6041

def b16700 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 70 140 25 49 224 224 224 480), lower := (rows 259 70 140 25 49 32 64 128 256), losses := [] }

theorem u16700 : Upper (D 8) (R 8) [258,68,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16701 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 140 25 81 160 224 160 416), lower := (rows 259 70 140 25 81 32 64 128 256), losses := [] }

theorem u16701 : Upper (D 8) (R 8) [258,68,136,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16702 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 140 25 112 161 225 161 417), lower := (rows 259 70 140 25 112 32 64 128 256), losses := [] }

theorem u16702 : Upper (D 8) (R 8) [258,68,136,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16703 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 70 140 25 145 96 96 224 352), lower := (rows 259 70 140 25 145 32 64 128 256), losses := [] }

theorem u16703 : Upper (D 8) (R 8) [258,68,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16704 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 140 25 176 97 97 225 353), lower := (rows 259 70 140 25 176 32 64 128 256), losses := [] }

theorem u16704 : Upper (D 8) (R 8) [258,68,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16705 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 140 25 208 33 97 161 289), lower := (rows 259 70 140 25 208 32 64 128 256), losses := [] }

theorem u16705 : Upper (D 8) (R 8) [258,68,136,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16706 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 70 140 41 49 240 240 240 496), lower := (rows 259 70 140 41 49 32 64 128 256), losses := [] }

theorem u16706 : Upper (D 8) (R 8) [258,68,136,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16707 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 140 41 81 176 240 176 432), lower := (rows 259 70 140 41 81 32 64 128 256), losses := [] }

theorem u16707 : Upper (D 8) (R 8) [258,68,136,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16708 : Route 9 := (fun mask => (mask,id))

def c16708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16708 : Upper (D 8) (R 8) [258,68,136,33,96] 13 := by
  apply FastRouting.sound _ _ [258,68,136,33,96] 13 (by decide) (choices 1) [1,16,128] r16708 c16708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6042
  · exact u6043
  · exact u6044

def b16709 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 259 70 140 41 145 112 112 240 368), lower := (rows 259 70 140 41 145 32 64 128 256), losses := [] }

theorem u16709 : Upper (D 8) (R 8) [258,68,136,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16710 : Route 9 := (fun mask => (mask,id))

def c16710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16710 : Upper (D 8) (R 8) [258,68,136,33,160] 13 := by
  apply FastRouting.sound _ _ [258,68,136,33,160] 13 (by decide) (choices 1) [1,16,64] r16710 c16710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6045
  · exact u6046
  · exact u6047

def r16711 : Route 9 := (fun mask => (mask,id))

def c16711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16711 : Upper (D 8) (R 8) [258,68,136,33,192] 13 := by
  apply FastRouting.sound _ _ [258,68,136,33,192] 13 (by decide) (choices 1) [1,16] r16711 c16711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6048
  · exact u6049

def b16712 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 140 56 49 225 225 225 481), lower := (rows 259 70 140 56 49 32 64 128 256), losses := [] }

theorem u16712 : Upper (D 8) (R 8) [258,68,136,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16713 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 140 56 81 161 225 161 417), lower := (rows 259 70 140 56 81 32 64 128 256), losses := [] }

theorem u16713 : Upper (D 8) (R 8) [258,68,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16714 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 140 56 112 161 225 161 417), lower := (rows 259 70 140 56 112 32 64 128 256), losses := [] }

theorem u16714 : Upper (D 8) (R 8) [258,68,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16715 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 140 56 145 97 97 225 353), lower := (rows 259 70 140 56 145 32 64 128 256), losses := [] }

theorem u16715 : Upper (D 8) (R 8) [258,68,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16716 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 70 140 56 176 97 97 225 353), lower := (rows 259 70 140 56 176 32 64 128 256), losses := [] }

theorem u16716 : Upper (D 8) (R 8) [258,68,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16717 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 140 56 208 33 97 161 289), lower := (rows 259 70 140 56 208 32 64 128 256), losses := [] }

theorem u16717 : Upper (D 8) (R 8) [258,68,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16718 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 259 70 164 25 25 224 224 224 480), lower := (rows 259 70 164 25 25 32 64 128 256), losses := [] }

theorem u16718 : Upper (D 8) (R 8) [258,68,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16719 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 70 164 25 49 232 232 232 488), lower := (rows 259 70 164 25 49 32 64 128 256), losses := [] }

theorem u16719 : Upper (D 8) (R 8) [258,68,160,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16720 : Route 9 := (fun mask => (mask,id))

def c16720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16720 : Upper (D 8) (R 8) [258,68,160,17,40] 13 := by
  apply FastRouting.sound _ _ [258,68,160,17,40] 13 (by decide) (choices 1) [1,64,128] r16720 c16720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6050
  · exact u6051
  · exact u6052

def b16721 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 164 25 81 168 232 168 424), lower := (rows 259 70 164 25 81 32 64 128 256), losses := [] }

theorem u16721 : Upper (D 8) (R 8) [258,68,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16722 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 164 25 88 161 225 161 417), lower := (rows 259 70 164 25 88 32 64 128 256), losses := [] }

theorem u16722 : Upper (D 8) (R 8) [258,68,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16723 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 164 25 112 169 233 169 425), lower := (rows 259 70 164 25 112 32 64 128 256), losses := [] }

theorem u16723 : Upper (D 8) (R 8) [258,68,160,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16724 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 164 25 145 104 104 232 360), lower := (rows 259 70 164 25 145 32 64 128 256), losses := [] }

theorem u16724 : Upper (D 8) (R 8) [258,68,160,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16725 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 164 25 152 97 97 225 353), lower := (rows 259 70 164 25 152 32 64 128 256), losses := [] }

theorem u16725 : Upper (D 8) (R 8) [258,68,160,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16726 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 164 25 176 105 105 233 361), lower := (rows 259 70 164 25 176 32 64 128 256), losses := [] }

theorem u16726 : Upper (D 8) (R 8) [258,68,160,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16727 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 164 25 208 41 105 169 297), lower := (rows 259 70 164 25 208 32 64 128 256), losses := [] }

theorem u16727 : Upper (D 8) (R 8) [258,68,160,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16728 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 70 164 41 49 248 216 216 472), lower := (rows 259 70 164 41 49 32 64 128 256), losses := [] }

theorem u16728 : Upper (D 8) (R 8) [258,68,160,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16729 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 164 41 56 241 209 209 465), lower := (rows 259 70 164 41 56 32 64 128 256), losses := [] }

theorem u16729 : Upper (D 8) (R 8) [258,68,160,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16730 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 164 41 81 184 248 184 440), lower := (rows 259 70 164 41 81 32 64 128 256), losses := [] }

theorem u16730 : Upper (D 8) (R 8) [258,68,160,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16731 : Route 9 := (fun mask => (mask,id))

def c16731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16731 : Upper (D 8) (R 8) [258,68,160,33,72] 13 := by
  apply FastRouting.sound _ _ [258,68,160,33,72] 13 (by decide) (choices 1) [1,16,128] r16731 c16731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6053
  · exact u6054
  · exact u6055

def r16732 : Route 9 := (fun mask => (mask,id))

def c16732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16732 : Upper (D 8) (R 8) [258,68,160,33,96] 13 := by
  apply FastRouting.sound _ _ [258,68,160,33,96] 13 (by decide) (choices 1) [1,8,16,128] r16732 c16732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6056
  · exact u6057
  · exact u6058
  · exact u6059

def b16733 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 259 70 164 41 145 120 120 248 376), lower := (rows 259 70 164 41 145 32 64 128 256), losses := [] }

theorem u16733 : Upper (D 8) (R 8) [258,68,160,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16734 : Route 9 := (fun mask => (mask,id))

def c16734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16734 : Upper (D 8) (R 8) [258,68,160,33,136] 13 := by
  apply FastRouting.sound _ _ [258,68,160,33,136] 13 (by decide) (choices 1) [1,16,64] r16734 c16734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6060
  · exact u6061
  · exact u6062

def b16735 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 164 41 176 121 89 217 345), lower := (rows 259 70 164 41 176 32 64 128 256), losses := [] }

theorem u16735 : Upper (D 8) (R 8) [258,68,160,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16736 : Route 9 := (fun mask => (mask,id))

def c16736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16736 : Upper (D 8) (R 8) [258,68,160,33,192] 13 := by
  apply FastRouting.sound _ _ [258,68,160,33,192] 13 (by decide) (choices 1) [1,8,16] r16736 c16736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6063
  · exact u6064
  · exact u6065

def b16737 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 164 56 56 225 193 193 449), lower := (rows 259 70 164 56 56 32 64 128 256), losses := [] }

theorem u16737 : Upper (D 8) (R 8) [258,68,160,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16738 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 164 56 81 169 233 169 425), lower := (rows 259 70 164 56 81 32 64 128 256), losses := [] }

theorem u16738 : Upper (D 8) (R 8) [258,68,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16739 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 164 56 88 161 225 161 417), lower := (rows 259 70 164 56 88 32 64 128 256), losses := [] }

theorem u16739 : Upper (D 8) (R 8) [258,68,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16739
end Delivery.IrregularNine14.P08
