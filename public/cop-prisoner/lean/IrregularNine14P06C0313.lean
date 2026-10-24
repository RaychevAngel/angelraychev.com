import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0091
import IrregularNine14P06C0092

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18780 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 41 274 36 65 193 321), lower := (rows 25 38 134 41 274 36 64 128 256), losses := [] }

theorem u18780 : Upper (D 6) (R 6) [24,36,130,33,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18781 : Route 9 := (fun mask => (mask,id))

def c18781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18781 : Upper (D 6) (R 6) [24,36,130,33,258,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,33,258,64] 13 (by decide) (choices 1) [1,4] r18781 c18781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5503
  · exact u5504

def b18782 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 38 134 41 276 33 66 194 322), lower := (rows 25 38 134 41 276 33 64 128 256), losses := [] }

theorem u18782 : Upper (D 6) (R 6) [24,36,130,33,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18783 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 41 276 34 65 193 321), lower := (rows 25 38 134 41 276 34 64 128 256), losses := [] }

theorem u18783 : Upper (D 6) (R 6) [24,36,130,33,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18784 : Route 9 := (fun mask => (mask,id))

def c18784 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18784 : Upper (D 6) (R 6) [24,36,130,33,260,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,33,260,64] 13 (by decide) (choices 1) [1,2] r18784 c18784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5505
  · exact u5506

def b18785 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 134 41 336 33 70 198 326), lower := (rows 25 38 134 41 336 33 64 128 256), losses := [] }

theorem u18785 : Upper (D 6) (R 6) [24,36,130,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18786 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 41 336 34 69 197 325), lower := (rows 25 38 134 41 336 34 64 128 256), losses := [] }

theorem u18786 : Upper (D 6) (R 6) [24,36,130,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18787 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 41 336 36 67 195 323), lower := (rows 25 38 134 41 336 36 64 128 256), losses := [] }

theorem u18787 : Upper (D 6) (R 6) [24,36,130,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18788 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 41 336 96 71 135 263), lower := (rows 25 38 134 41 336 96 64 128 256), losses := [] }

theorem u18788 : Upper (D 6) (R 6) [24,36,130,33,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18789 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 345, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 134 73 273 34 100 228 356), lower := (rows 25 38 134 73 273 34 64 128 256), losses := [] }

theorem u18789 : Upper (D 6) (R 6) [24,36,130,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18790 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 134 73 273 36 98 226 354), lower := (rows 25 38 134 73 273 36 64 128 256), losses := [] }

theorem u18790 : Upper (D 6) (R 6) [24,36,130,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18791 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 5, region := 134, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 73 273 96 102 166 294), lower := (rows 25 38 134 73 273 96 64 128 256), losses := [] }

theorem u18791 : Upper (D 6) (R 6) [24,36,130,65,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18792 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 73 274 33 100 228 356), lower := (rows 25 38 134 73 274 33 64 128 256), losses := [] }

theorem u18792 : Upper (D 6) (R 6) [24,36,130,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18793 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 73 274 36 97 225 353), lower := (rows 25 38 134 73 274 36 64 128 256), losses := [] }

theorem u18793 : Upper (D 6) (R 6) [24,36,130,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18794 : Route 9 := (fun mask => (mask,id))

def c18794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18794 : Upper (D 6) (R 6) [24,36,130,65,258,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,65,258,64] 13 (by decide) (choices 1) [1,4,32] r18794 c18794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5507
  · exact u5508
  · exact u5509

def b18795 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 73 276 33 98 226 354), lower := (rows 25 38 134 73 276 33 64 128 256), losses := [] }

theorem u18795 : Upper (D 6) (R 6) [24,36,130,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18796 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 73 276 34 97 225 353), lower := (rows 25 38 134 73 276 34 64 128 256), losses := [] }

theorem u18796 : Upper (D 6) (R 6) [24,36,130,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18797 : Route 9 := (fun mask => (mask,id))

def c18797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18797 : Upper (D 6) (R 6) [24,36,130,65,260,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,65,260,64] 13 (by decide) (choices 1) [1,2,32] r18797 c18797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5510
  · exact u5511
  · exact u5512

def b18798 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 73 304 33 70 198 326), lower := (rows 25 38 134 73 304 33 64 128 256), losses := [] }

theorem u18798 : Upper (D 6) (R 6) [24,36,130,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18799 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 73 304 34 69 197 325), lower := (rows 25 38 134 73 304 34 64 128 256), losses := [] }

theorem u18799 : Upper (D 6) (R 6) [24,36,130,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18800 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 73 304 36 67 195 323), lower := (rows 25 38 134 73 304 36 64 128 256), losses := [] }

theorem u18800 : Upper (D 6) (R 6) [24,36,130,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18801 : Route 9 := (fun mask => (mask,id))

def c18801 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18801 : Upper (D 6) (R 6) [24,36,130,65,288,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,65,288,64] 13 (by decide) (choices 1) [1,2,4] r18801 c18801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5513
  · exact u5514
  · exact u5515

def b18802 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 25 38 134 74 84 33 353 417 289), lower := (rows 25 38 134 74 84 33 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 18 41 105 169 297), good := (rows 505 500 148 505 84 481 64 128 256) }] }

theorem u18802 : Upper (D 6) (R 6) [24,36,130,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18803 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 25 38 134 74 84 288 97 161 289), lower := (rows 25 38 134 74 84 288 64 128 256), losses := [] }

theorem u18803 : Upper (D 6) (R 6) [24,36,130,66,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18803 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18804 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 74 112 33 325 389 261), lower := (rows 25 38 134 74 112 33 64 128 256), losses := [] }

theorem u18804 : Upper (D 6) (R 6) [24,36,130,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18805 : PairBound 9 := { available := 257, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 74 112 36 321 385 257), lower := (rows 25 38 134 74 112 36 64 128 256), losses := [] }

theorem u18805 : Upper (D 6) (R 6) [24,36,130,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18806 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 25 38 134 74 112 288 69 133 261), lower := (rows 25 38 134 74 112 288 64 128 256), losses := [] }

theorem u18806 : Upper (D 6) (R 6) [24,36,130,66,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18806 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18807 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 134 74 273 33 100 228 356), lower := (rows 25 38 134 74 273 33 64 128 256), losses := [] }

theorem u18807 : Upper (D 6) (R 6) [24,36,130,66,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18808 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 74 273 36 97 225 353), lower := (rows 25 38 134 74 273 36 64 128 256), losses := [] }

theorem u18808 : Upper (D 6) (R 6) [24,36,130,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18809 : Route 9 := (fun mask => (mask,id))

def c18809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18809 : Upper (D 6) (R 6) [24,36,130,66,257,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,257,64] 13 (by decide) (choices 1) [1,4,32] r18809 c18809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5516
  · exact u5517
  · exact u5518

def b18810 : PairBound 9 := { available := 97, camps := [], pairs := [(0,1),(3,2),(4,1)], upper := (rows 25 38 134 74 276 33 97 225 353), lower := (rows 25 38 134 74 276 33 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 18 41 105 169 297), good := (rows 505 500 148 505 276 481 64 128 256) },{ target := 2, region := (rows 1 2 0 10 16 33 97 161 289), good := (rows 505 490 138 74 272 481 64 128 256) }] }

theorem u18810 : Upper (D 6) (R 6) [24,36,130,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18811 : Route 9 := (fun mask => (mask,id))

def c18811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18811 : Upper (D 6) (R 6) [24,36,130,66,260,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,260,64] 13 (by decide) (choices 1) [1,32] r18811 c18811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5519
  · exact u5520

def r18812 : Route 9 := (fun mask => (mask,id))

def c18812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18812 : Upper (D 6) (R 6) [24,36,130,66,288,1] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,288,1] 13 (by decide) (choices 1) [1,4] r18812 c18812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5521
  · exact u5522

def b18813 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 74 304 36 65 193 321), lower := (rows 25 38 134 74 304 36 64 128 256), losses := [] }

theorem u18813 : Upper (D 6) (R 6) [24,36,130,66,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18814 : Route 9 := (fun mask => (mask,id))

def c18814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18814 : Upper (D 6) (R 6) [24,36,130,66,288,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,288,64] 13 (by decide) (choices 1) [1,4] r18814 c18814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5523
  · exact u5524

def r18815 : Route 9 := (fun mask => (mask,id))

def c18815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18815 : Upper (D 6) (R 6) [24,36,130,66,320,1] 13 := by
  apply FastRouting.sound _ _ [24,36,130,66,320,1] 13 (by decide) (choices 1) [1,4,32] r18815 c18815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5525
  · exact u5526
  · exact u5527

def b18816 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 74 336 36 97 161 289), lower := (rows 25 38 134 74 336 36 64 128 256), losses := [] }

theorem u18816 : Upper (D 6) (R 6) [24,36,130,66,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18817 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 76 112 33 323 387 259), lower := (rows 25 38 134 76 112 33 64 128 256), losses := [] }

theorem u18817 : Upper (D 6) (R 6) [24,36,130,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18818 : PairBound 9 := { available := 257, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 76 112 34 321 385 257), lower := (rows 25 38 134 76 112 34 64 128 256), losses := [] }

theorem u18818 : Upper (D 6) (R 6) [24,36,130,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18819 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 25 38 134 76 112 288 67 131 259), lower := (rows 25 38 134 76 112 288 64 128 256), losses := [] }

theorem u18819 : Upper (D 6) (R 6) [24,36,130,68,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18819 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18820 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 134 76 273 33 98 226 354), lower := (rows 25 38 134 76 273 33 64 128 256), losses := [] }

theorem u18820 : Upper (D 6) (R 6) [24,36,130,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18821 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 76 273 34 97 225 353), lower := (rows 25 38 134 76 273 34 64 128 256), losses := [] }

theorem u18821 : Upper (D 6) (R 6) [24,36,130,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18822 : Route 9 := (fun mask => (mask,id))

def c18822 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18822 : Upper (D 6) (R 6) [24,36,130,68,257,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,257,64] 13 (by decide) (choices 1) [1,2,32] r18822 c18822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5528
  · exact u5529
  · exact u5530

def b18823 : PairBound 9 := { available := 97, camps := [], pairs := [(0,1),(3,1),(4,2)], upper := (rows 25 38 134 76 274 33 97 225 353), lower := (rows 25 38 134 76 274 33 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 10 16 49 113 177 305), good := (rows 505 492 140 76 505 481 64 128 256) },{ target := 2, region := (rows 1 2 0 8 18 33 97 161 289), good := (rows 505 498 146 72 274 481 64 128 256) }] }

theorem u18823 : Upper (D 6) (R 6) [24,36,130,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18824 : Route 9 := (fun mask => (mask,id))

def c18824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18824 : Upper (D 6) (R 6) [24,36,130,68,258,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,258,64] 13 (by decide) (choices 1) [1,32] r18824 c18824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5531
  · exact u5532

def r18825 : Route 9 := (fun mask => (mask,id))

def c18825 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18825 : Upper (D 6) (R 6) [24,36,130,68,288,1] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,288,1] 13 (by decide) (choices 1) [1,2] r18825 c18825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5533
  · exact u5534

def b18826 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 76 304 34 65 193 321), lower := (rows 25 38 134 76 304 34 64 128 256), losses := [] }

theorem u18826 : Upper (D 6) (R 6) [24,36,130,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18827 : Route 9 := (fun mask => (mask,id))

def c18827 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18827 : Upper (D 6) (R 6) [24,36,130,68,288,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,288,64] 13 (by decide) (choices 1) [1,2] r18827 c18827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5535
  · exact u5536

def r18828 : Route 9 := (fun mask => (mask,id))

def c18828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18828 : Upper (D 6) (R 6) [24,36,130,68,320,1] 13 := by
  apply FastRouting.sound _ _ [24,36,130,68,320,1] 13 (by decide) (choices 1) [1,2,32] r18828 c18828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5537
  · exact u5538
  · exact u5539

def b18829 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 76 336 34 97 161 289), lower := (rows 25 38 134 76 336 34 64 128 256), losses := [] }

theorem u18829 : Upper (D 6) (R 6) [24,36,130,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18830 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 134 104 273 33 70 198 326), lower := (rows 25 38 134 104 273 33 64 128 256), losses := [] }

theorem u18830 : Upper (D 6) (R 6) [24,36,130,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18831 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 104 273 34 69 197 325), lower := (rows 25 38 134 104 273 34 64 128 256), losses := [] }

theorem u18831 : Upper (D 6) (R 6) [24,36,130,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18832 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 104 273 36 67 195 323), lower := (rows 25 38 134 104 273 36 64 128 256), losses := [] }

theorem u18832 : Upper (D 6) (R 6) [24,36,130,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18833 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 134 104 273 96 71 135 263), lower := (rows 25 38 134 104 273 96 64 128 256), losses := [] }

theorem u18833 : Upper (D 6) (R 6) [24,36,130,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18834 : Route 9 := (fun mask => (mask,id))

def c18834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18834 : Upper (D 6) (R 6) [24,36,130,96,258,1] 13 := by
  apply FastRouting.sound _ _ [24,36,130,96,258,1] 13 (by decide) (choices 1) [1,4] r18834 c18834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5540
  · exact u5541

def b18835 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 104 274 36 65 193 321), lower := (rows 25 38 134 104 274 36 64 128 256), losses := [] }

theorem u18835 : Upper (D 6) (R 6) [24,36,130,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18836 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 134 104 274 96 69 133 261), lower := (rows 25 38 134 104 274 96 64 128 256), losses := [] }

theorem u18836 : Upper (D 6) (R 6) [24,36,130,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18837 : Route 9 := (fun mask => (mask,id))

def c18837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18837 : Upper (D 6) (R 6) [24,36,130,96,260,1] 13 := by
  apply FastRouting.sound _ _ [24,36,130,96,260,1] 13 (by decide) (choices 1) [1,2] r18837 c18837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5542
  · exact u5543

def b18838 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 104 276 34 65 193 321), lower := (rows 25 38 134 104 276 34 64 128 256), losses := [] }

theorem u18838 : Upper (D 6) (R 6) [24,36,130,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18839 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 134 104 276 96 67 131 259), lower := (rows 25 38 134 104 276 96 64 128 256), losses := [] }

theorem u18839 : Upper (D 6) (R 6) [24,36,130,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18839
end Delivery.IrregularNine14.P06
