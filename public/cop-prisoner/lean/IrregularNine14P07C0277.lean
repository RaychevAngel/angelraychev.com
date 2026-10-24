import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0063
import IrregularNine14P07C0064

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16620 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 13 98 21 41 146 288 194 194 450), lower := (rows 13 98 21 41 146 288 64 128 256), losses := [] }

theorem u16620 : Upper (D 7) (R 7) [12,96,17,33,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16620 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16621 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 21 41 208 34 450 386 386), lower := (rows 13 98 21 41 208 34 64 128 256), losses := [] }

theorem u16621 : Upper (D 7) (R 7) [12,96,17,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16622 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 41 208 160 322 386 258), lower := (rows 13 98 21 41 208 160 64 128 256), losses := [] }

theorem u16622 : Upper (D 7) (R 7) [12,96,17,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16623 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 13 98 21 41 208 288 194 130 386), lower := (rows 13 98 21 41 208 288 64 128 256), losses := [] }

theorem u16623 : Upper (D 7) (R 7) [12,96,17,33,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16623 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16624 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 21 41 274 34 192 192 448), lower := (rows 13 98 21 41 274 34 64 128 256), losses := [] }

theorem u16624 : Upper (D 7) (R 7) [12,96,17,33,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16625 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 41 274 96 194 130 386), lower := (rows 13 98 21 41 274 96 64 128 256), losses := [] }

theorem u16625 : Upper (D 7) (R 7) [12,96,17,33,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16626 : Route 9 := (fun mask => (mask,id))

def c16626 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16626 : Upper (D 7) (R 7) [12,96,17,33,258,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,33,258,128] 13 (by decide) (choices 1) [2,128] r16626 c16626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3816
  · exact u3817

def b16627 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 21 41 336 34 194 130 386), lower := (rows 13 98 21 41 336 34 64 128 256), losses := [] }

theorem u16627 : Upper (D 7) (R 7) [12,96,17,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16628 : Route 9 := (fun mask => (mask,id))

def c16628 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16628 : Upper (D 7) (R 7) [12,96,17,33,320,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,33,320,128] 13 (by decide) (choices 1) [2,128] r16628 c16628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3818
  · exact u3819

def b16629 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 21 41 400 34 194 194 450), lower := (rows 13 98 21 41 400 34 64 128 256), losses := [] }

theorem u16629 : Upper (D 7) (R 7) [12,96,17,33,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16630 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 41 400 96 194 130 386), lower := (rows 13 98 21 41 400 96 64 128 256), losses := [] }

theorem u16630 : Upper (D 7) (R 7) [12,96,17,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16631 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 41 400 160 66 194 322), lower := (rows 13 98 21 41 400 160 64 128 256), losses := [] }

theorem u16631 : Upper (D 7) (R 7) [12,96,17,33,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16632 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(4,0)], upper := (rows 13 98 21 137 274 34 224 224 480), lower := (rows 13 98 21 137 274 34 64 128 256), losses := [{ target := 1, region := (rows 21 0 20 24 16 32 98 162 290), good := (rows 13 480 29 137 477 480 64 128 256) }] }

theorem u16632 : Upper (D 7) (R 7) [12,96,17,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16633 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 137 274 96 226 162 418), lower := (rows 13 98 21 137 274 96 64 128 256), losses := [] }

theorem u16633 : Upper (D 7) (R 7) [12,96,17,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16634 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 338, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 21 137 274 160 98 226 354), lower := (rows 13 98 21 137 274 160 64 128 256), losses := [] }

theorem u16634 : Upper (D 7) (R 7) [12,96,17,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16635 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,5),(1,0),(1,7),(4,0)], upper := (rows 13 98 21 137 304 34 194 194 450), lower := (rows 13 98 21 137 304 34 64 128 256), losses := [{ target := 5, region := (rows 21 2 20 24 16 0 98 162 290), good := (rows 13 450 29 137 477 450 64 128 256) }] }

theorem u16635 : Upper (D 7) (R 7) [12,96,17,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16636 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 137 304 96 194 130 386), lower := (rows 13 98 21 137 304 96 64 128 256), losses := [] }

theorem u16636 : Upper (D 7) (R 7) [12,96,17,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16637 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 338, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 21 137 304 160 66 194 322), lower := (rows 13 98 21 137 304 160 64 128 256), losses := [] }

theorem u16637 : Upper (D 7) (R 7) [12,96,17,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16638 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 138 176 33 322 450 322), lower := (rows 13 98 21 138 176 33 64 128 256), losses := [] }

theorem u16638 : Upper (D 7) (R 7) [12,96,17,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16639 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 13 98 21 138 176 34 321 449 321), lower := (rows 13 98 21 138 176 34 64 128 256), losses := [] }

theorem u16639 : Upper (D 7) (R 7) [12,96,17,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16640 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 138 176 96 323 387 259), lower := (rows 13 98 21 138 176 96 64 128 256), losses := [] }

theorem u16640 : Upper (D 7) (R 7) [12,96,17,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16641 : Route 9 := (fun mask => (mask,id))

def c16641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16641 : Upper (D 7) (R 7) [12,96,17,130,160,256] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,160,256] 13 (by decide) (choices 1) [1,2] r16641 c16641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3820
  · exact u3821

def r16642 : Route 9 := (fun mask => (mask,id))

def c16642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16642 : Upper (D 7) (R 7) [12,96,17,130,258,1] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,258,1] 13 (by decide) (choices 1) [32,128] r16642 c16642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3822
  · exact u3823

def b16643 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 138 274 96 225 161 417), lower := (rows 13 98 21 138 274 96 64 128 256), losses := [] }

theorem u16643 : Upper (D 7) (R 7) [12,96,17,130,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16644_1 : Upper (D 7) (R 7) [12,96,17,130,258,128,1] 13 :=
  permutation_upper _ _ _ [12,96,17,130,258,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3823

theorem m16644_32 : Upper (D 7) (R 7) [12,96,17,130,258,128,32] 13 :=
  permutation_upper _ _ _ [12,96,17,130,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3824

def r16644 : Route 9 := (fun mask => (mask,id))

def c16644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16644 : Upper (D 7) (R 7) [12,96,17,130,258,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,258,128] 13 (by decide) (choices 1) [1,32] r16644 c16644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16644_1
  · exact m16644_32

def b16645 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 21 138 304 33 194 194 450), lower := (rows 13 98 21 138 304 33 64 128 256), losses := [] }

theorem u16645 : Upper (D 7) (R 7) [12,96,17,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16646 : Route 9 := (fun mask => (mask,id))

def c16646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16646 : Upper (D 7) (R 7) [12,96,17,130,288,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,288,2] 13 (by decide) (choices 1) [1,128] r16646 c16646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3825
  · exact u3826

def b16647 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 138 304 96 195 131 387), lower := (rows 13 98 21 138 304 96 64 128 256), losses := [] }

theorem u16647 : Upper (D 7) (R 7) [12,96,17,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16648 : Route 9 := (fun mask => (mask,id))

def c16648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16648 : Upper (D 7) (R 7) [12,96,17,130,288,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,288,128] 13 (by decide) (choices 1) [1,2] r16648 c16648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3827
  · exact u3828

def b16649 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 138 400 33 98 226 354), lower := (rows 13 98 21 138 400 33 64 128 256), losses := [] }

theorem u16649 : Upper (D 7) (R 7) [12,96,17,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16650_1 : Upper (D 7) (R 7) [12,96,17,130,384,2,1] 13 :=
  permutation_upper _ _ _ [12,96,17,130,384,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3829

def r16650 : Route 9 := (fun mask => (mask,id))

def c16650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16650 : Upper (D 7) (R 7) [12,96,17,130,384,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,384,2] 13 (by decide) (choices 1) [1,32] r16650 c16650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16650_1
  · exact u3830

def b16651 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 138 400 96 99 163 291), lower := (rows 13 98 21 138 400 96 64 128 256), losses := [] }

theorem u16651 : Upper (D 7) (R 7) [12,96,17,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16652 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 168 146 33 322 450 322), lower := (rows 13 98 21 168 146 33 64 128 256), losses := [] }

theorem u16652 : Upper (D 7) (R 7) [12,96,17,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16653 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 98 21 168 146 34 321 449 321), lower := (rows 13 98 21 168 146 34 64 128 256), losses := [] }

theorem u16653 : Upper (D 7) (R 7) [12,96,17,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16654 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 168 146 96 323 387 259), lower := (rows 13 98 21 168 146 96 64 128 256), losses := [] }

theorem u16654 : Upper (D 7) (R 7) [12,96,17,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16655 : Route 9 := (fun mask => (mask,id))

def c16655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16655 : Upper (D 7) (R 7) [12,96,17,160,130,256] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,130,256] 13 (by decide) (choices 1) [1,2] r16655 c16655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3831
  · exact u3832

def b16656 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 168 208 33 322 386 258), lower := (rows 13 98 21 168 208 33 64 128 256), losses := [] }

theorem u16656 : Upper (D 7) (R 7) [12,96,17,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16657 : Route 9 := (fun mask => (mask,id))

def c16657 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u16657 : Upper (D 7) (R 7) [12,96,17,160,192,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,192,2] 13 (by decide) (choices 1) [1,2,256] r16657 c16657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3833
  · exact u3834
  · exact u3835

def r16658 : Route 9 := (fun mask => (mask,id))

def c16658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16658 : Upper (D 7) (R 7) [12,96,17,160,192,256] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,192,256] 13 (by decide) (choices 1) [1,2] r16658 c16658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3836
  · exact u3837

def b16659 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 21 168 274 33 194 194 450), lower := (rows 13 98 21 168 274 33 64 128 256), losses := [] }

theorem u16659 : Upper (D 7) (R 7) [12,96,17,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16660 : Route 9 := (fun mask => (mask,id))

def c16660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16660 : Upper (D 7) (R 7) [12,96,17,160,258,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,258,2] 13 (by decide) (choices 1) [1,128] r16660 c16660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3838
  · exact u3839

def b16661 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 168 274 96 195 131 387), lower := (rows 13 98 21 168 274 96 64 128 256), losses := [] }

theorem u16661 : Upper (D 7) (R 7) [12,96,17,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16662 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 21 168 274 160 67 195 323), lower := (rows 13 98 21 168 274 160 64 128 256), losses := [] }

theorem u16662 : Upper (D 7) (R 7) [12,96,17,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16663 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 21 168 336 33 194 130 386), lower := (rows 13 98 21 168 336 33 64 128 256), losses := [] }

theorem u16663 : Upper (D 7) (R 7) [12,96,17,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16664 : Route 9 := (fun mask => (mask,id))

def c16664 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16664 : Upper (D 7) (R 7) [12,96,17,160,320,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,320,2] 13 (by decide) (choices 1) [1,2,128] r16664 c16664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3840
  · exact u3841
  · exact u3842

def b16665 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 21 168 336 160 67 131 259), lower := (rows 13 98 21 168 336 160 64 128 256), losses := [] }

theorem u16665 : Upper (D 7) (R 7) [12,96,17,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16666 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 168 400 33 66 194 322), lower := (rows 13 98 21 168 400 33 64 128 256), losses := [] }

theorem u16666 : Upper (D 7) (R 7) [12,96,17,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16667 : Route 9 := (fun mask => (mask,id))

def c16667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16667 : Upper (D 7) (R 7) [12,96,17,160,384,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,384,2] 13 (by decide) (choices 1) [1,2] r16667 c16667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3843
  · exact u3844

def b16668 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 168 400 96 67 131 259), lower := (rows 13 98 21 168 400 96 64 128 256), losses := [] }

theorem u16668 : Upper (D 7) (R 7) [12,96,17,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16669 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(4,0)], upper := (rows 13 98 21 265 146 34 224 224 480), lower := (rows 13 98 21 265 146 34 64 128 256), losses := [{ target := 1, region := (rows 21 0 20 24 16 32 98 162 290), good := (rows 13 480 29 265 477 480 64 128 256) }] }

theorem u16669 : Upper (D 7) (R 7) [12,96,17,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16670 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 265 146 96 226 162 418), lower := (rows 13 98 21 265 146 96 64 128 256), losses := [] }

theorem u16670 : Upper (D 7) (R 7) [12,96,17,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16671 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 13 98 21 265 146 160 98 226 354), lower := (rows 13 98 21 265 146 160 64 128 256), losses := [{ target := 7, region := (rows 21 34 20 24 16 32 98 0 290), good := (rows 13 354 29 265 351 354 64 0 256) }] }

theorem u16671 : Upper (D 7) (R 7) [12,96,17,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16672 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,5),(1,0),(1,7),(4,0)], upper := (rows 13 98 21 265 176 34 194 194 450), lower := (rows 13 98 21 265 176 34 64 128 256), losses := [{ target := 5, region := (rows 21 2 20 24 16 0 98 162 290), good := (rows 13 450 29 265 477 450 64 128 256) }] }

theorem u16672 : Upper (D 7) (R 7) [12,96,17,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16673 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 265 176 96 194 130 386), lower := (rows 13 98 21 265 176 96 64 128 256), losses := [] }

theorem u16673 : Upper (D 7) (R 7) [12,96,17,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16674 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 21 265 176 160 66 194 322), lower := (rows 13 98 21 265 176 160 64 128 256), losses := [] }

theorem u16674 : Upper (D 7) (R 7) [12,96,17,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16675 : Route 9 := (fun mask => (mask,id))

def c16675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16675 : Upper (D 7) (R 7) [12,96,17,258,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,17,258,130,1] 13 (by decide) (choices 1) [32,128] r16675 c16675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3845
  · exact u3846

def b16676 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 266 146 96 225 161 417), lower := (rows 13 98 21 266 146 96 64 128 256), losses := [] }

theorem u16676 : Upper (D 7) (R 7) [12,96,17,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16677_1 : Upper (D 7) (R 7) [12,96,17,258,130,128,1] 13 :=
  permutation_upper _ _ _ [12,96,17,258,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3846

theorem m16677_32 : Upper (D 7) (R 7) [12,96,17,258,130,128,32] 13 :=
  permutation_upper _ _ _ [12,96,17,258,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3847

def r16677 : Route 9 := (fun mask => (mask,id))

def c16677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16677 : Upper (D 7) (R 7) [12,96,17,258,130,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,258,130,128] 13 (by decide) (choices 1) [1,32] r16677 c16677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16677_1
  · exact m16677_32

def b16678 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 21 266 176 33 194 194 450), lower := (rows 13 98 21 266 176 33 64 128 256), losses := [] }

theorem u16678 : Upper (D 7) (R 7) [12,96,17,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16679 : Route 9 := (fun mask => (mask,id))

def c16679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16679 : Upper (D 7) (R 7) [12,96,17,258,160,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,258,160,2] 13 (by decide) (choices 1) [1,128] r16679 c16679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3848
  · exact u3849

#print axioms u16679
end Delivery.IrregularNine14.P07
