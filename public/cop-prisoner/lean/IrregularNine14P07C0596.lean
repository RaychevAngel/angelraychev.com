import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0351
import IrregularNine14P07C0352

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35760 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 262 13 88 50 225 193 193 449), lower := (rows 35 262 13 88 50 32 64 128 256), losses := [] }

theorem u35760 : Upper (D 7) (R 7) [34,260,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35761 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 35 262 13 88 81 162 226 162 418), lower := (rows 35 262 13 88 81 32 64 128 256), losses := [] }

theorem u35761 : Upper (D 7) (R 7) [34,260,9,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35762 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 262 13 88 82 161 225 161 417), lower := (rows 35 262 13 88 82 32 64 128 256), losses := [] }

theorem u35762 : Upper (D 7) (R 7) [34,260,9,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35763 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 262 13 88 112 163 195 131 387), lower := (rows 35 262 13 88 112 32 64 128 256), losses := [] }

theorem u35763 : Upper (D 7) (R 7) [34,260,9,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35764 : Route 9 := (fun mask => (mask,id))

def c35764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35764 : Upper (D 7) (R 7) [34,260,9,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80,129] 13 (by decide) (choices 1) [2,64,128] r35764 c35764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21071
  · exact u21072
  · exact u21073

def r35765 : Route 9 := (fun mask => (mask,id))

def c35765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35765 : Upper (D 7) (R 7) [34,260,9,80,130] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80,130] 13 (by decide) (choices 1) [1,64,128] r35765 c35765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21074
  · exact u21075
  · exact u21076

def r35766 : Route 9 := (fun mask => (mask,id))

def c35766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35766 : Upper (D 7) (R 7) [34,260,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80,160] 13 (by decide) (choices 1) [1,2,64,128] r35766 c35766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21077
  · exact u21078
  · exact u21079
  · exact u21080

def b35767 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 262 13 88 208 163 227 163 419), lower := (rows 35 262 13 88 208 32 64 128 256), losses := [] }

theorem u35767 : Upper (D 7) (R 7) [34,260,9,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35768 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 35 262 13 104 19 240 208 208 464), lower := (rows 35 262 13 104 19 32 64 128 256), losses := [] }

theorem u35768 : Upper (D 7) (R 7) [34,260,9,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35769 : Route 9 := (fun mask => (mask,id))

def c35769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35769 : Upper (D 7) (R 7) [34,260,9,96,65] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,65] 13 (by decide) (choices 1) [2,16,128] r35769 c35769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21081
  · exact u21082
  · exact u21083

def r35770 : Route 9 := (fun mask => (mask,id))

def c35770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35770 : Upper (D 7) (R 7) [34,260,9,96,66] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,66] 13 (by decide) (choices 1) [1,16,128] r35770 c35770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21084
  · exact u21085
  · exact u21086

def r35771 : Route 9 := (fun mask => (mask,id))

def c35771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35771 : Upper (D 7) (R 7) [34,260,9,96,129] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,129] 13 (by decide) (choices 1) [2,16,64,128] r35771 c35771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21087
  · exact u21088
  · exact u21089
  · exact u21090

def r35772 : Route 9 := (fun mask => (mask,id))

def c35772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35772 : Upper (D 7) (R 7) [34,260,9,96,130] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,130] 13 (by decide) (choices 1) [1,16,64,128] r35772 c35772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21091
  · exact u21092
  · exact u21093
  · exact u21094

def r35773 : Route 9 := (fun mask => (mask,id))

def c35773 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35773 : Upper (D 7) (R 7) [34,260,9,96,192] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,192] 13 (by decide) (choices 1) [1,2,16,128] r35773 c35773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21095
  · exact u21096
  · exact u21097
  · exact u21098

def b35774 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 262 13 200 19 240 240 240 496), lower := (rows 35 262 13 200 19 32 64 128 256), losses := [] }

theorem u35774 : Upper (D 7) (R 7) [34,260,9,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35775 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 262 13 200 49 242 210 210 466), lower := (rows 35 262 13 200 49 32 64 128 256), losses := [] }

theorem u35775 : Upper (D 7) (R 7) [34,260,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35776 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 262 13 200 50 241 209 209 465), lower := (rows 35 262 13 200 50 32 64 128 256), losses := [] }

theorem u35776 : Upper (D 7) (R 7) [34,260,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35777 : Route 9 := (fun mask => (mask,id))

def c35777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35777 : Upper (D 7) (R 7) [34,260,9,192,65] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192,65] 13 (by decide) (choices 1) [2,16,128] r35777 c35777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21099
  · exact u21100
  · exact u21101

def r35778 : Route 9 := (fun mask => (mask,id))

def c35778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35778 : Upper (D 7) (R 7) [34,260,9,192,66] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192,66] 13 (by decide) (choices 1) [1,16,128] r35778 c35778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21102
  · exact u21103
  · exact u21104

def r35779 : Route 9 := (fun mask => (mask,id))

def c35779 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35779 : Upper (D 7) (R 7) [34,260,9,192,96] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192,96] 13 (by decide) (choices 1) [1,2,16,128] r35779 c35779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21105
  · exact u21106
  · exact u21107
  · exact u21108

def b35780 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 35 262 13 200 208 51 115 179 307), lower := (rows 35 262 13 200 208 32 64 128 256), losses := [] }

theorem u35780 : Upper (D 7) (R 7) [34,260,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35781 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 262 14 25 49 224 192 192 448), lower := (rows 35 262 14 25 49 32 64 128 256), losses := [] }

theorem u35781 : Upper (D 7) (R 7) [34,260,10,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35782 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 0, region := 216, targets := 2 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 14 25 81 224 224 224 480), lower := (rows 35 262 14 25 81 32 64 128 256), losses := [] }

theorem u35782 : Upper (D 7) (R 7) [34,260,10,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35783 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 262 14 25 112 225 193 193 449), lower := (rows 35 262 14 25 112 32 64 128 256), losses := [] }

theorem u35783 : Upper (D 7) (R 7) [34,260,10,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35784 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35784 : Upper (D 7) (R 7) [34,260,10,17,192] 13 := by
  apply FastRouting.sound _ _ [34,260,10,17,192] 13 (by decide) (choices 1) [1,64] r35784 c35784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21109
  · exact u21110

def b35785 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,5),(3,1),(4,1),(4,5)], upper := (rows 35 262 14 56 81 225 193 193 449), lower := (rows 35 262 14 56 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 17 0 81 145 273), good := (rows 467 262 14 478 465 0 64 128 256) }] }

theorem u35785 : Upper (D 7) (R 7) [34,260,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35786 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35786 : Upper (D 7) (R 7) [34,260,10,48,192] 13 := by
  apply FastRouting.sound _ _ [34,260,10,48,192] 13 (by decide) (choices 1) [1,64] r35786 c35786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21111
  · exact u21112

def b35787 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 216, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(3,5)], upper := (rows 35 262 14 73 49 240 208 208 464), lower := (rows 35 262 14 73 49 32 64 128 256), losses := [] }

theorem u35787 : Upper (D 7) (R 7) [34,260,10,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35788 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 16, targets := 160 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 35 262 14 73 81 176 240 176 432), lower := (rows 35 262 14 73 81 32 64 128 256), losses := [] }

theorem u35788 : Upper (D 7) (R 7) [34,260,10,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35789 : Route 9 := (fun mask => (mask,id))

def c35789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35789 : Upper (D 7) (R 7) [34,260,10,65,96] 13 := by
  apply FastRouting.sound _ _ [34,260,10,65,96] 13 (by decide) (choices 1) [1,16,128] r35789 c35789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21113
  · exact u21114
  · exact u21115

def r35790 : Route 9 := (fun mask => (mask,id))

def c35790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35790 : Upper (D 7) (R 7) [34,260,10,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,10,65,129] 13 (by decide) (choices 1) [16,64,128] r35790 c35790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21116
  · exact u21117
  · exact u21118

def r35791 : Route 9 := (fun mask => (mask,id))

def c35791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35791 : Upper (D 7) (R 7) [34,260,10,65,160] 13 := by
  apply FastRouting.sound _ _ [34,260,10,65,160] 13 (by decide) (choices 1) [1,16,64,128] r35791 c35791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21119
  · exact u21120
  · exact u21121
  · exact u21122

def r35792 : Route 9 := (fun mask => (mask,id))

def c35792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35792 : Upper (D 7) (R 7) [34,260,10,65,192] 13 := by
  apply FastRouting.sound _ _ [34,260,10,65,192] 13 (by decide) (choices 1) [1,16,128] r35792 c35792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21123
  · exact u21124
  · exact u21125

def b35793 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 216, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(3,5)], upper := (rows 35 262 14 88 49 225 193 193 449), lower := (rows 35 262 14 88 49 32 64 128 256), losses := [] }

theorem u35793 : Upper (D 7) (R 7) [34,260,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35794 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 4, region := 8, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 35 262 14 88 81 161 225 161 417), lower := (rows 35 262 14 88 81 32 64 128 256), losses := [] }

theorem u35794 : Upper (D 7) (R 7) [34,260,10,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35795 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 262 14 88 112 161 193 129 385), lower := (rows 35 262 14 88 112 32 64 128 256), losses := [] }

theorem u35795 : Upper (D 7) (R 7) [34,260,10,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35796 : Route 9 := (fun mask => (mask,id))

def c35796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35796 : Upper (D 7) (R 7) [34,260,10,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,10,80,129] 13 (by decide) (choices 1) [1,64,128] r35796 c35796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21126
  · exact u21127
  · exact u21128

def r35797 : Route 9 := (fun mask => (mask,id))

def c35797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35797 : Upper (D 7) (R 7) [34,260,10,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,10,80,160] 13 (by decide) (choices 1) [1,64,128] r35797 c35797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21129
  · exact u21130
  · exact u21131

def b35798 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 262 14 88 208 161 225 161 417), lower := (rows 35 262 14 88 208 32 64 128 256), losses := [] }

theorem u35798 : Upper (D 7) (R 7) [34,260,10,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35799 : Route 9 := (fun mask => (mask,id))

def c35799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35799 : Upper (D 7) (R 7) [34,260,10,96,65] 13 := by
  apply FastRouting.sound _ _ [34,260,10,96,65] 13 (by decide) (choices 1) [1,16,128] r35799 c35799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21132
  · exact u21133
  · exact u21134

def r35800 : Route 9 := (fun mask => (mask,id))

def c35800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35800 : Upper (D 7) (R 7) [34,260,10,96,129] 13 := by
  apply FastRouting.sound _ _ [34,260,10,96,129] 13 (by decide) (choices 1) [1,16,64,128] r35800 c35800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21135
  · exact u21136
  · exact u21137
  · exact u21138

def r35801 : Route 9 := (fun mask => (mask,id))

def c35801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35801 : Upper (D 7) (R 7) [34,260,10,96,192] 13 := by
  apply FastRouting.sound _ _ [34,260,10,96,192] 13 (by decide) (choices 1) [1,16,128] r35801 c35801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21139
  · exact u21140
  · exact u21141

def b35802 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 216, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(3,5)], upper := (rows 35 262 14 200 49 241 209 209 465), lower := (rows 35 262 14 200 49 32 64 128 256), losses := [] }

theorem u35802 : Upper (D 7) (R 7) [34,260,10,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35803 : Route 9 := (fun mask => (mask,id))

def c35803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35803 : Upper (D 7) (R 7) [34,260,10,192,65] 13 := by
  apply FastRouting.sound _ _ [34,260,10,192,65] 13 (by decide) (choices 1) [1,16,128] r35803 c35803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21142
  · exact u21143
  · exact u21144

def r35804 : Route 9 := (fun mask => (mask,id))

def c35804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35804 : Upper (D 7) (R 7) [34,260,10,192,96] 13 := by
  apply FastRouting.sound _ _ [34,260,10,192,96] 13 (by decide) (choices 1) [1,16,128] r35804 c35804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21145
  · exact u21146
  · exact u21147

def b35805 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 35 262 14 200 208 49 113 177 305), lower := (rows 35 262 14 200 208 32 64 128 256), losses := [] }

theorem u35805 : Upper (D 7) (R 7) [34,260,10,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35806 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 28 11 81 224 224 224 480), lower := (rows 35 262 28 11 81 32 64 128 256), losses := [] }

theorem u35806 : Upper (D 7) (R 7) [34,260,24,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35807 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 35 262 28 11 112 225 193 193 449), lower := (rows 35 262 28 11 112 32 64 128 256), losses := [] }

theorem u35807 : Upper (D 7) (R 7) [34,260,24,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35808 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 28 11 208 225 225 225 481), lower := (rows 35 262 28 11 208 32 64 128 256), losses := [] }

theorem u35808 : Upper (D 7) (R 7) [34,260,24,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35809 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 28 41 81 226 194 194 450), lower := (rows 35 262 28 41 81 32 64 128 256), losses := [] }

theorem u35809 : Upper (D 7) (R 7) [34,260,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35810 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,5)], upper := (rows 35 262 28 41 82 225 193 193 449), lower := (rows 35 262 28 41 82 32 64 128 256), losses := [] }

theorem u35810 : Upper (D 7) (R 7) [34,260,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35811 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 28 41 208 227 195 195 451), lower := (rows 35 262 28 41 208 32 64 128 256), losses := [] }

theorem u35811 : Upper (D 7) (R 7) [34,260,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35812 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 28 42 81 225 193 193 449), lower := (rows 35 262 28 42 81 32 64 128 256), losses := [] }

theorem u35812 : Upper (D 7) (R 7) [34,260,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35813 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 28 42 208 225 193 193 449), lower := (rows 35 262 28 42 208 32 64 128 256), losses := [] }

theorem u35813 : Upper (D 7) (R 7) [34,260,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35814 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 20, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(4,1)], upper := (rows 35 262 28 73 81 162 226 162 418), lower := (rows 35 262 28 73 81 32 64 128 256), losses := [] }

theorem u35814 : Upper (D 7) (R 7) [34,260,24,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35815 : Route 9 := (fun mask => (mask,id))

def c35815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35815 : Upper (D 7) (R 7) [34,260,24,65,66] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,66] 13 (by decide) (choices 1) [1,128] r35815 c35815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21148
  · exact u21149

def r35816 : Route 9 := (fun mask => (mask,id))

def c35816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35816 : Upper (D 7) (R 7) [34,260,24,65,96] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,96] 13 (by decide) (choices 1) [1,2,128] r35816 c35816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21150
  · exact u21151
  · exact u21152

theorem m35817_128 : Upper (D 7) (R 7) [34,260,24,65,129,128] 13 :=
  permutation_upper _ _ _ [34,260,24,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u21154

def r35817 : Route 9 := (fun mask => (mask,id))

def c35817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35817 : Upper (D 7) (R 7) [34,260,24,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,129] 13 (by decide) (choices 1) [2,64,128] r35817 c35817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21153
  · exact u21154
  · exact m35817_128

def r35818 : Route 9 := (fun mask => (mask,id))

def c35818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35818 : Upper (D 7) (R 7) [34,260,24,65,130] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,130] 13 (by decide) (choices 1) [1,64,128] r35818 c35818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21155
  · exact u21156
  · exact u21157

def r35819 : Route 9 := (fun mask => (mask,id))

def c35819 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35819 : Upper (D 7) (R 7) [34,260,24,65,160] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,160] 13 (by decide) (choices 1) [1,2,64,128] r35819 c35819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21158
  · exact u21159
  · exact u21160
  · exact u21161

#print axioms u35819
end Delivery.IrregularNine14.P07
