import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0085
import IrregularNine14P07C0086

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18780 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 266 176 160 81 209 337), lower := (rows 35 70 13 266 176 160 64 128 256), losses := [] }

theorem u18780 : Upper (D 7) (R 7) [34,68,9,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18781 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 266 208 33 240 176 432), lower := (rows 35 70 13 266 208 33 64 128 256), losses := [] }

theorem u18781 : Upper (D 7) (R 7) [34,68,9,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18782 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,6),(3,6),(4,1)], upper := (rows 35 70 13 266 208 48 225 161 417), lower := (rows 35 70 13 266 208 48 64 128 256), losses := [] }

theorem u18782 : Upper (D 7) (R 7) [34,68,9,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18782 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18783 : Route 9 := (fun mask => (mask,id))

def c18783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18783 : Upper (D 7) (R 7) [34,68,9,258,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,192,128] 13 (by decide) (choices 1) [1,16,32] r18783 c18783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5142
  · exact u5143
  · exact u5144

def b18784 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,0),(4,0),(4,7)], upper := (rows 35 70 13 280 112 33 194 130 386), lower := (rows 35 70 13 280 112 33 64 128 256), losses := [] }

theorem u18784 : Upper (D 7) (R 7) [34,68,9,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18785 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 280 112 34 193 129 385), lower := (rows 35 70 13 280 112 34 64 128 256), losses := [] }

theorem u18785 : Upper (D 7) (R 7) [34,68,9,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18786 : Route 9 := (fun mask => (mask,id))

def c18786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18786 : Upper (D 7) (R 7) [34,68,9,272,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,96,128] 13 (by decide) (choices 1) [1,2,128] r18786 c18786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5145
  · exact u5146
  · exact u5147

def b18787 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 280 145 34 224 224 480), lower := (rows 35 70 13 280 145 34 64 128 256), losses := [] }

theorem u18787 : Upper (D 7) (R 7) [34,68,9,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18788 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 280 145 96 226 162 418), lower := (rows 35 70 13 280 145 96 64 128 256), losses := [] }

theorem u18788 : Upper (D 7) (R 7) [34,68,9,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18789 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 280 145 160 98 226 354), lower := (rows 35 70 13 280 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 183 71 135 263), good := (rows 482 486 494 312 504 160 64 160 256) },{ target := 7, region := (rows 1 22 20 24 16 32 65 0 257), good := (rows 355 70 335 286 351 32 64 0 256) }] }

theorem u18789 : Upper (D 7) (R 7) [34,68,9,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18790 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 13 280 146 33 224 224 480), lower := (rows 35 70 13 280 146 33 64 128 256), losses := [] }

theorem u18790 : Upper (D 7) (R 7) [34,68,9,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18791 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 280 146 96 225 161 417), lower := (rows 35 70 13 280 146 96 64 128 256), losses := [] }

theorem u18791 : Upper (D 7) (R 7) [34,68,9,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18792 : Route 9 := (fun mask => (mask,id))

def c18792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18792 : Upper (D 7) (R 7) [34,68,9,272,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,130,128] 13 (by decide) (choices 1) [1,32] r18792 c18792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5148
  · exact u5149

def b18793 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 13 280 176 33 194 194 450), lower := (rows 35 70 13 280 176 33 64 128 256), losses := [] }

theorem u18793 : Upper (D 7) (R 7) [34,68,9,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18794 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 280 176 34 193 193 449), lower := (rows 35 70 13 280 176 34 64 128 256), losses := [] }

theorem u18794 : Upper (D 7) (R 7) [34,68,9,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18795 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 280 176 96 195 131 387), lower := (rows 35 70 13 280 176 96 64 128 256), losses := [] }

theorem u18795 : Upper (D 7) (R 7) [34,68,9,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18796 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 280 176 160 67 195 323), lower := (rows 35 70 13 280 176 160 64 128 256), losses := [] }

theorem u18796 : Upper (D 7) (R 7) [34,68,9,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18797 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 13 280 208 33 226 162 418), lower := (rows 35 70 13 280 208 33 64 128 256), losses := [] }

theorem u18797 : Upper (D 7) (R 7) [34,68,9,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18798 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 280 208 34 225 161 417), lower := (rows 35 70 13 280 208 34 64 128 256), losses := [] }

theorem u18798 : Upper (D 7) (R 7) [34,68,9,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18799 : Route 9 := (fun mask => (mask,id))

def c18799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18799 : Upper (D 7) (R 7) [34,68,9,272,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,192,128] 13 (by decide) (choices 1) [1,2,32] r18799 c18799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5150
  · exact u5151
  · exact u5152

def b18800 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 296 81 34 208 144 400), lower := (rows 35 70 13 296 81 34 64 128 256), losses := [] }

theorem u18800 : Upper (D 7) (R 7) [34,68,9,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18801 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 13 296 81 48 194 130 386), lower := (rows 35 70 13 296 81 48 64 128 256), losses := [] }

theorem u18801 : Upper (D 7) (R 7) [34,68,9,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18801 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18802 : Route 9 := (fun mask => (mask,id))

def c18802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18802 : Upper (D 7) (R 7) [34,68,9,288,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,65,128] 13 (by decide) (choices 1) [2,16,128] r18802 c18802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5153
  · exact u5154
  · exact u5155

def b18803 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 296 145 34 208 208 464), lower := (rows 35 70 13 296 145 34 64 128 256), losses := [] }

theorem u18803 : Upper (D 7) (R 7) [34,68,9,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18804 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 0, region := 456, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 35 70 13 296 145 48 194 194 450), lower := (rows 35 70 13 296 145 48 64 128 256), losses := [] }

theorem u18804 : Upper (D 7) (R 7) [34,68,9,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18804 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18805 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 296 145 96 210 146 402), lower := (rows 35 70 13 296 145 96 64 128 256), losses := [] }

theorem u18805 : Upper (D 7) (R 7) [34,68,9,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18806 : Route 9 := (fun mask => (mask,id))

def c18806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18806 : Upper (D 7) (R 7) [34,68,9,288,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,129,128] 13 (by decide) (choices 1) [2,16] r18806 c18806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5156
  · exact u5157

def b18807 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 296 146 33 208 208 464), lower := (rows 35 70 13 296 146 33 64 128 256), losses := [] }

theorem u18807 : Upper (D 7) (R 7) [34,68,9,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18808 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 70 13 296 146 48 193 193 449), lower := (rows 35 70 13 296 146 48 64 128 256), losses := [] }

theorem u18808 : Upper (D 7) (R 7) [34,68,9,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18808 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18809 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 296 146 96 209 145 401), lower := (rows 35 70 13 296 146 96 64 128 256), losses := [] }

theorem u18809 : Upper (D 7) (R 7) [34,68,9,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18810 : Route 9 := (fun mask => (mask,id))

def c18810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18810 : Upper (D 7) (R 7) [34,68,9,288,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,130,128] 13 (by decide) (choices 1) [1,16] r18810 c18810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5158
  · exact u5159

def b18811 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 296 208 33 210 146 402), lower := (rows 35 70 13 296 208 33 64 128 256), losses := [] }

theorem u18811 : Upper (D 7) (R 7) [34,68,9,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18812 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 296 208 34 209 145 401), lower := (rows 35 70 13 296 208 34 64 128 256), losses := [] }

theorem u18812 : Upper (D 7) (R 7) [34,68,9,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18813 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6)], upper := (rows 35 70 13 296 208 48 195 131 387), lower := (rows 35 70 13 296 208 48 64 128 256), losses := [] }

theorem u18813 : Upper (D 7) (R 7) [34,68,9,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18813 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18814 : Route 9 := (fun mask => (mask,id))

def c18814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18814 : Upper (D 7) (R 7) [34,68,9,288,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,192,128] 13 (by decide) (choices 1) [1,2,16] r18814 c18814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5160
  · exact u5161
  · exact u5162

def b18815 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 328 145 34 240 176 432), lower := (rows 35 70 13 328 145 34 64 128 256), losses := [] }

theorem u18815 : Upper (D 7) (R 7) [34,68,9,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18816 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,6),(3,0),(4,6)], upper := (rows 35 70 13 328 145 48 226 162 418), lower := (rows 35 70 13 328 145 48 64 128 256), losses := [] }

theorem u18816 : Upper (D 7) (R 7) [34,68,9,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18816 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18817 : Route 9 := (fun mask => (mask,id))

def c18817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18817 : Upper (D 7) (R 7) [34,68,9,320,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,320,129,128] 13 (by decide) (choices 1) [2,16,32] r18817 c18817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5163
  · exact u5164
  · exact u5165

def b18818 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 328 146 33 240 176 432), lower := (rows 35 70 13 328 146 33 64 128 256), losses := [] }

theorem u18818 : Upper (D 7) (R 7) [34,68,9,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18819 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 13 328 146 48 225 161 417), lower := (rows 35 70 13 328 146 48 64 128 256), losses := [] }

theorem u18819 : Upper (D 7) (R 7) [34,68,9,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18819 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18820 : Route 9 := (fun mask => (mask,id))

def c18820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18820 : Upper (D 7) (R 7) [34,68,9,320,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,320,130,128] 13 (by decide) (choices 1) [1,16,32] r18820 c18820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5166
  · exact u5167
  · exact u5168

def b18821 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 328 176 33 210 146 402), lower := (rows 35 70 13 328 176 33 64 128 256), losses := [] }

theorem u18821 : Upper (D 7) (R 7) [34,68,9,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18822 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 328 176 34 209 145 401), lower := (rows 35 70 13 328 176 34 64 128 256), losses := [] }

theorem u18822 : Upper (D 7) (R 7) [34,68,9,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18823 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 328 176 48 195 131 387), lower := (rows 35 70 13 328 176 48 64 128 256), losses := [] }

theorem u18823 : Upper (D 7) (R 7) [34,68,9,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18823 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18824 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 13 328 176 160 83 147 275), lower := (rows 35 70 13 328 176 160 64 128 256), losses := [] }

theorem u18824 : Upper (D 7) (R 7) [34,68,9,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18825 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 392 81 34 240 176 432), lower := (rows 35 70 13 392 81 34 64 128 256), losses := [] }

theorem u18825 : Upper (D 7) (R 7) [34,68,9,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18826 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 13 392 81 48 226 162 418), lower := (rows 35 70 13 392 81 48 64 128 256), losses := [] }

theorem u18826 : Upper (D 7) (R 7) [34,68,9,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18826 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18827 : Route 9 := (fun mask => (mask,id))

def c18827 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18827 : Upper (D 7) (R 7) [34,68,9,384,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,65,128] 13 (by decide) (choices 1) [2,16,32] r18827 c18827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5169
  · exact u5170
  · exact u5171

def b18828 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(3,0),(4,0),(4,7)], upper := (rows 35 70 13 392 112 33 210 146 402), lower := (rows 35 70 13 392 112 33 64 128 256), losses := [] }

theorem u18828 : Upper (D 7) (R 7) [34,68,9,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18829 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 392 112 34 209 145 401), lower := (rows 35 70 13 392 112 34 64 128 256), losses := [] }

theorem u18829 : Upper (D 7) (R 7) [34,68,9,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18830 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 392 112 48 195 131 387), lower := (rows 35 70 13 392 112 48 64 128 256), losses := [] }

theorem u18830 : Upper (D 7) (R 7) [34,68,9,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18830 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18831 : Route 9 := (fun mask => (mask,id))

def c18831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18831 : Upper (D 7) (R 7) [34,68,9,384,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,96,128] 13 (by decide) (choices 1) [1,2,16] r18831 c18831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5172
  · exact u5173
  · exact u5174

def b18832 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 392 145 34 112 240 368), lower := (rows 35 70 13 392 145 34 64 128 256), losses := [] }

theorem u18832 : Upper (D 7) (R 7) [34,68,9,384,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18833 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 35 70 13 392 145 48 98 226 354), lower := (rows 35 70 13 392 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 29 16 48 65 129 257), good := (rows 490 78 462 392 504 56 64 128 256) },{ target := 7, region := (rows 1 6 4 8 16 48 65 0 257), good := (rows 355 70 335 264 369 48 64 0 256) }] }

theorem u18833 : Upper (D 7) (R 7) [34,68,9,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18833 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18834 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 392 145 96 114 178 306), lower := (rows 35 70 13 392 145 96 64 128 256), losses := [] }

theorem u18834 : Upper (D 7) (R 7) [34,68,9,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18835 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 13 392 146 33 112 240 368), lower := (rows 35 70 13 392 146 33 64 128 256), losses := [] }

theorem u18835 : Upper (D 7) (R 7) [34,68,9,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18836 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 13 392 146 48 97 225 353), lower := (rows 35 70 13 392 146 48 64 128 256), losses := [] }

theorem u18836 : Upper (D 7) (R 7) [34,68,9,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18836 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18837 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 392 146 96 113 177 305), lower := (rows 35 70 13 392 146 96 64 128 256), losses := [] }

theorem u18837 : Upper (D 7) (R 7) [34,68,9,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18838 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 13 392 176 33 82 210 338), lower := (rows 35 70 13 392 176 33 64 128 256), losses := [] }

theorem u18838 : Upper (D 7) (R 7) [34,68,9,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18839 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 392 176 34 81 209 337), lower := (rows 35 70 13 392 176 34 64 128 256), losses := [] }

theorem u18839 : Upper (D 7) (R 7) [34,68,9,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18839
end Delivery.IrregularNine14.P07
