import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0101

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16740 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 164 56 112 169 201 137 393), lower := (rows 259 70 164 56 112 32 64 128 256), losses := [] }

theorem u16740 : Upper (D 8) (R 8) [258,68,160,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16741 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 259 70 164 56 145 105 105 233 361), lower := (rows 259 70 164 56 145 32 64 128 256), losses := [] }

theorem u16741 : Upper (D 8) (R 8) [258,68,160,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16742 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 164 56 152 97 97 225 353), lower := (rows 259 70 164 56 152 32 64 128 256), losses := [] }

theorem u16742 : Upper (D 8) (R 8) [258,68,160,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16743 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 164 56 176 105 73 201 329), lower := (rows 259 70 164 56 176 32 64 128 256), losses := [] }

theorem u16743 : Upper (D 8) (R 8) [258,68,160,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16744 : Route 9 := (fun mask => (mask,id))

def c16744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16744 : Upper (D 8) (R 8) [258,68,160,48,192] 13 := by
  apply FastRouting.sound _ _ [258,68,160,48,192] 13 (by decide) (choices 1) [1,8] r16744 c16744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6066
  · exact u6067

def b16745 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 164 73 152 49 113 177 305), lower := (rows 259 70 164 73 152 32 64 128 256), losses := [] }

theorem u16745 : Upper (D 8) (R 8) [258,68,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16746 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 259 70 164 88 145 41 105 169 297), lower := (rows 259 70 164 88 145 32 64 128 256), losses := [] }

theorem u16746 : Upper (D 8) (R 8) [258,68,160,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16747 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 164 88 152 33 97 161 289), lower := (rows 259 70 164 88 152 32 64 128 256), losses := [] }

theorem u16747 : Upper (D 8) (R 8) [258,68,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16748 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 164 88 176 41 105 169 297), lower := (rows 259 70 164 88 176 32 64 128 256), losses := [] }

theorem u16748 : Upper (D 8) (R 8) [258,68,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16749 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 259 70 164 104 145 57 121 185 313), lower := (rows 259 70 164 104 145 32 64 128 256), losses := [] }

theorem u16749 : Upper (D 8) (R 8) [258,68,160,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16750 : Route 9 := (fun mask => (mask,id))

def c16750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16750 : Upper (D 8) (R 8) [258,68,160,96,136] 13 := by
  apply FastRouting.sound _ _ [258,68,160,96,136] 13 (by decide) (choices 1) [1,16] r16750 c16750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6068
  · exact u6069

def b16751 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 164 104 176 57 89 153 281), lower := (rows 259 70 164 104 176 32 64 128 256), losses := [] }

theorem u16751 : Upper (D 8) (R 8) [258,68,160,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16752 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 13 176 240 240 240 496), lower := (rows 259 98 13 13 176 32 64 128 256), losses := [] }

theorem u16752 : Upper (D 8) (R 8) [258,96,9,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16753 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 13 208 176 240 176 432), lower := (rows 259 98 13 13 208 32 64 128 256), losses := [] }

theorem u16753 : Upper (D 8) (R 8) [258,96,9,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16754 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 25 52 224 224 224 480), lower := (rows 259 98 13 25 52 32 64 128 256), losses := [] }

theorem u16754 : Upper (D 8) (R 8) [258,96,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16755 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 25 84 160 224 160 416), lower := (rows 259 98 13 25 84 32 64 128 256), losses := [] }

theorem u16755 : Upper (D 8) (R 8) [258,96,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16756 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 25 148 224 224 224 480), lower := (rows 259 98 13 25 148 32 64 128 256), losses := [] }

theorem u16756 : Upper (D 8) (R 8) [258,96,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16757 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 25 176 228 228 228 484), lower := (rows 259 98 13 25 176 32 64 128 256), losses := [] }

theorem u16757 : Upper (D 8) (R 8) [258,96,9,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16758 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 25 208 164 228 164 420), lower := (rows 259 98 13 25 208 32 64 128 256), losses := [] }

theorem u16758 : Upper (D 8) (R 8) [258,96,9,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16759 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 28 49 224 224 224 480), lower := (rows 259 98 13 28 49 32 64 128 256), losses := [] }

theorem u16759 : Upper (D 8) (R 8) [258,96,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16760 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 28 81 160 224 160 416), lower := (rows 259 98 13 28 81 32 64 128 256), losses := [] }

theorem u16760 : Upper (D 8) (R 8) [258,96,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16761 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 13 28 112 161 225 161 417), lower := (rows 259 98 13 28 112 32 64 128 256), losses := [] }

theorem u16761 : Upper (D 8) (R 8) [258,96,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16762 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 28 145 224 224 224 480), lower := (rows 259 98 13 28 145 32 64 128 256), losses := [] }

theorem u16762 : Upper (D 8) (R 8) [258,96,9,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16763 : Route 9 := (fun mask => (mask,id))

def c16763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16763 : Upper (D 8) (R 8) [258,96,9,20,160] 13 := by
  apply FastRouting.sound _ _ [258,96,9,20,160] 13 (by decide) (choices 1) [1,64,128] r16763 c16763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6070
  · exact u6071
  · exact u6072

def b16764 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 28 208 161 225 161 417), lower := (rows 259 98 13 28 208 32 64 128 256), losses := [] }

theorem u16764 : Upper (D 8) (R 8) [258,96,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16765 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 41 52 240 208 208 464), lower := (rows 259 98 13 41 52 32 64 128 256), losses := [] }

theorem u16765 : Upper (D 8) (R 8) [258,96,9,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16766 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 84 176 240 176 432), lower := (rows 259 98 13 41 84 32 64 128 256), losses := [] }

theorem u16766 : Upper (D 8) (R 8) [258,96,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16766 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16767 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 148 240 240 240 496), lower := (rows 259 98 13 41 148 32 64 128 256), losses := [] }

theorem u16767 : Upper (D 8) (R 8) [258,96,9,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16768 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 176 244 212 212 468), lower := (rows 259 98 13 41 176 32 64 128 256), losses := [] }

theorem u16768 : Upper (D 8) (R 8) [258,96,9,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16769 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 208 180 244 180 436), lower := (rows 259 98 13 41 208 32 64 128 256), losses := [] }

theorem u16769 : Upper (D 8) (R 8) [258,96,9,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16770 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 44 49 240 208 208 464), lower := (rows 259 98 13 44 49 32 64 128 256), losses := [] }

theorem u16770 : Upper (D 8) (R 8) [258,96,9,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16771 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 44 81 176 240 176 432), lower := (rows 259 98 13 44 81 32 64 128 256), losses := [] }

theorem u16771 : Upper (D 8) (R 8) [258,96,9,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16772 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 13 44 112 177 209 145 401), lower := (rows 259 98 13 44 112 32 64 128 256), losses := [] }

theorem u16772 : Upper (D 8) (R 8) [258,96,9,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16773 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 44 145 240 240 240 496), lower := (rows 259 98 13 44 145 32 64 128 256), losses := [] }

theorem u16773 : Upper (D 8) (R 8) [258,96,9,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16774 : Route 9 := (fun mask => (mask,id))

def c16774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16774 : Upper (D 8) (R 8) [258,96,9,36,160] 13 := by
  apply FastRouting.sound _ _ [258,96,9,36,160] 13 (by decide) (choices 1) [1,16,64,128] r16774 c16774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6073
  · exact u6074
  · exact u6075
  · exact u6076

def r16775 : Route 9 := (fun mask => (mask,id))

def c16775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16775 : Upper (D 8) (R 8) [258,96,9,36,192] 13 := by
  apply FastRouting.sound _ _ [258,96,9,36,192] 13 (by decide) (choices 1) [1,16,128] r16775 c16775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6077
  · exact u6078
  · exact u6079

def b16776 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 56 49 228 196 196 452), lower := (rows 259 98 13 56 49 32 64 128 256), losses := [] }

theorem u16776 : Upper (D 8) (R 8) [258,96,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16777 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 56 52 225 193 193 449), lower := (rows 259 98 13 56 52 32 64 128 256), losses := [] }

theorem u16777 : Upper (D 8) (R 8) [258,96,9,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16778 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 56 81 164 228 164 420), lower := (rows 259 98 13 56 81 32 64 128 256), losses := [] }

theorem u16778 : Upper (D 8) (R 8) [258,96,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16779 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 56 84 161 225 161 417), lower := (rows 259 98 13 56 84 32 64 128 256), losses := [] }

theorem u16779 : Upper (D 8) (R 8) [258,96,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16780 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 56 112 165 197 133 389), lower := (rows 259 98 13 56 112 32 64 128 256), losses := [] }

theorem u16780 : Upper (D 8) (R 8) [258,96,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16781 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 56 145 228 228 228 484), lower := (rows 259 98 13 56 145 32 64 128 256), losses := [] }

theorem u16781 : Upper (D 8) (R 8) [258,96,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16782 : Route 9 := (fun mask => (mask,id))

def c16782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16782 : Upper (D 8) (R 8) [258,96,9,48,132] 13 := by
  apply FastRouting.sound _ _ [258,96,9,48,132] 13 (by decide) (choices 1) [1,64,128] r16782 c16782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6080
  · exact u6081
  · exact u6082

def b16783 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 56 176 229 197 197 453), lower := (rows 259 98 13 56 176 32 64 128 256), losses := [] }

theorem u16783 : Upper (D 8) (R 8) [258,96,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16784 : Route 9 := (fun mask => (mask,id))

def c16784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16784 : Upper (D 8) (R 8) [258,96,9,48,192] 13 := by
  apply FastRouting.sound _ _ [258,96,9,48,192] 13 (by decide) (choices 1) [1,4,128] r16784 c16784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6083
  · exact u6084
  · exact u6085

def b16785 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 73 52 176 240 176 432), lower := (rows 259 98 13 73 52 32 64 128 256), losses := [] }

theorem u16785 : Upper (D 8) (R 8) [258,96,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16786 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 73 148 176 240 176 432), lower := (rows 259 98 13 73 148 32 64 128 256), losses := [] }

theorem u16786 : Upper (D 8) (R 8) [258,96,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16787 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 73 176 180 244 180 436), lower := (rows 259 98 13 73 176 32 64 128 256), losses := [] }

theorem u16787 : Upper (D 8) (R 8) [258,96,9,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16788 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 76 49 176 240 176 432), lower := (rows 259 98 13 76 49 32 64 128 256), losses := [] }

theorem u16788 : Upper (D 8) (R 8) [258,96,9,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16789 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 76 145 176 240 176 432), lower := (rows 259 98 13 76 145 32 64 128 256), losses := [] }

theorem u16789 : Upper (D 8) (R 8) [258,96,9,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16790 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 76 176 177 241 177 433), lower := (rows 259 98 13 76 176 32 64 128 256), losses := [] }

theorem u16790 : Upper (D 8) (R 8) [258,96,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16791 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 88 49 164 228 164 420), lower := (rows 259 98 13 88 49 32 64 128 256), losses := [] }

theorem u16791 : Upper (D 8) (R 8) [258,96,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16792 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 88 52 161 225 161 417), lower := (rows 259 98 13 88 52 32 64 128 256), losses := [] }

theorem u16792 : Upper (D 8) (R 8) [258,96,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16793 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 88 145 164 228 164 420), lower := (rows 259 98 13 88 145 32 64 128 256), losses := [] }

theorem u16793 : Upper (D 8) (R 8) [258,96,9,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16794 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 88 148 161 225 161 417), lower := (rows 259 98 13 88 148 32 64 128 256), losses := [] }

theorem u16794 : Upper (D 8) (R 8) [258,96,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16795 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 13 88 176 165 229 165 421), lower := (rows 259 98 13 88 176 32 64 128 256), losses := [] }

theorem u16795 : Upper (D 8) (R 8) [258,96,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16796 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 104 49 180 212 148 404), lower := (rows 259 98 13 104 49 32 64 128 256), losses := [] }

theorem u16796 : Upper (D 8) (R 8) [258,96,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16797 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 104 52 177 209 145 401), lower := (rows 259 98 13 104 52 32 64 128 256), losses := [] }

theorem u16797 : Upper (D 8) (R 8) [258,96,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16798 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 104 145 180 244 180 436), lower := (rows 259 98 13 104 145 32 64 128 256), losses := [] }

theorem u16798 : Upper (D 8) (R 8) [258,96,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16799 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 104 148 177 241 177 433), lower := (rows 259 98 13 104 148 32 64 128 256), losses := [] }

theorem u16799 : Upper (D 8) (R 8) [258,96,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16799
end Delivery.IrregularNine14.P08
