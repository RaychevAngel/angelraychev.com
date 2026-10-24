import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0064

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16680 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 266 176 96 195 131 387), lower := (rows 13 98 21 266 176 96 64 128 256), losses := [] }

theorem u16680 : Upper (D 7) (R 7) [12,96,17,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16681 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 21 266 176 160 67 195 323), lower := (rows 13 98 21 266 176 160 64 128 256), losses := [] }

theorem u16681 : Upper (D 7) (R 7) [12,96,17,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16682 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 21 296 146 33 194 194 450), lower := (rows 13 98 21 296 146 33 64 128 256), losses := [] }

theorem u16682 : Upper (D 7) (R 7) [12,96,17,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16683 : Route 9 := (fun mask => (mask,id))

def c16683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16683 : Upper (D 7) (R 7) [12,96,17,288,130,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288,130,2] 13 (by decide) (choices 1) [1,128] r16683 c16683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3850
  · exact u3851

def b16684 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 296 146 96 195 131 387), lower := (rows 13 98 21 296 146 96 64 128 256), losses := [] }

theorem u16684 : Upper (D 7) (R 7) [12,96,17,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16685 : Route 9 := (fun mask => (mask,id))

def c16685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16685 : Upper (D 7) (R 7) [12,96,17,288,130,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288,130,128] 13 (by decide) (choices 1) [1,2] r16685 c16685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3852
  · exact u3853

def b16686 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 21 296 208 33 194 130 386), lower := (rows 13 98 21 296 208 33 64 128 256), losses := [] }

theorem u16686 : Upper (D 7) (R 7) [12,96,17,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16687 : Route 9 := (fun mask => (mask,id))

def c16687 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16687 : Upper (D 7) (R 7) [12,96,17,288,192,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288,192,2] 13 (by decide) (choices 1) [1,2,128] r16687 c16687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3854
  · exact u3855
  · exact u3856

def r16688 : Route 9 := (fun mask => (mask,id))

def c16688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16688 : Upper (D 7) (R 7) [12,96,17,288,192,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288,192,128] 13 (by decide) (choices 1) [1,2] r16688 c16688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3857
  · exact u3858

def b16689 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 392 146 33 98 226 354), lower := (rows 13 98 21 392 146 33 64 128 256), losses := [] }

theorem u16689 : Upper (D 7) (R 7) [12,96,17,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16690_1 : Upper (D 7) (R 7) [12,96,17,384,130,2,1] 13 :=
  permutation_upper _ _ _ [12,96,17,384,130,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3859

def r16690 : Route 9 := (fun mask => (mask,id))

def c16690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16690 : Upper (D 7) (R 7) [12,96,17,384,130,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,384,130,2] 13 (by decide) (choices 1) [1,32] r16690 c16690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16690_1
  · exact u3860

def b16691 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 392 146 96 99 163 291), lower := (rows 13 98 21 392 146 96 64 128 256), losses := [] }

theorem u16691 : Upper (D 7) (R 7) [12,96,17,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16692 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 392 176 33 66 194 322), lower := (rows 13 98 21 392 176 33 64 128 256), losses := [] }

theorem u16692 : Upper (D 7) (R 7) [12,96,17,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16693 : Route 9 := (fun mask => (mask,id))

def c16693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16693 : Upper (D 7) (R 7) [12,96,17,384,160,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,384,160,2] 13 (by decide) (choices 1) [1,2] r16693 c16693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3861
  · exact u3862

def b16694 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 392 176 96 67 131 259), lower := (rows 13 98 21 392 176 96 64 128 256), losses := [] }

theorem u16694 : Upper (D 7) (R 7) [12,96,17,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16695 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 98 22 41 145 34 448 448 448), lower := (rows 13 98 22 41 145 34 64 128 256), losses := [] }

theorem u16695 : Upper (D 7) (R 7) [12,96,18,33,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16696 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 41 145 96 450 386 386), lower := (rows 13 98 22 41 145 96 64 128 256), losses := [] }

theorem u16696 : Upper (D 7) (R 7) [12,96,18,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16697 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 4, region := 40, targets := 66 }], pairs := [(1,0),(2,0),(3,1),(3,6)], upper := (rows 13 98 22 41 145 160 322 450 322), lower := (rows 13 98 22 41 145 160 64 128 256), losses := [] }

theorem u16697 : Upper (D 7) (R 7) [12,96,18,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16698 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0),(4,5)], upper := (rows 13 98 22 41 145 288 194 194 450), lower := (rows 13 98 22 41 145 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 70 134 262), good := (rows 477 450 470 25 145 256 64 128 256) }] }

theorem u16698 : Upper (D 7) (R 7) [12,96,18,33,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16698 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16699 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 13 98 22 41 208 33 450 386 386), lower := (rows 13 98 22 41 208 33 64 128 256), losses := [] }

theorem u16699 : Upper (D 7) (R 7) [12,96,18,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16700 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 22 41 208 34 449 385 385), lower := (rows 13 98 22 41 208 34 64 128 256), losses := [] }

theorem u16700 : Upper (D 7) (R 7) [12,96,18,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16701 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(2,0),(3,6)], upper := (rows 13 98 22 41 208 160 323 387 259), lower := (rows 13 98 22 41 208 160 64 128 256), losses := [] }

theorem u16701 : Upper (D 7) (R 7) [12,96,18,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16702 : Route 9 := (fun mask => (mask,id))

def c16702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16702 : Upper (D 7) (R 7) [12,96,18,33,192,256] 13 := by
  apply FastRouting.sound _ _ [12,96,18,33,192,256] 13 (by decide) (choices 1) [1,2,128] r16702 c16702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3863
  · exact u3864
  · exact u3865

def b16703 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 98 22 41 273 34 192 192 448), lower := (rows 13 98 22 41 273 34 64 128 256), losses := [] }

theorem u16703 : Upper (D 7) (R 7) [12,96,18,33,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16704 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 41 273 96 194 130 386), lower := (rows 13 98 22 41 273 96 64 128 256), losses := [] }

theorem u16704 : Upper (D 7) (R 7) [12,96,18,33,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16705 : Route 9 := (fun mask => (mask,id))

def c16705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16705 : Upper (D 7) (R 7) [12,96,18,33,257,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,33,257,128] 13 (by decide) (choices 1) [2,128] r16705 c16705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3866
  · exact u3867

def b16706 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 13 98 22 41 336 33 194 130 386), lower := (rows 13 98 22 41 336 33 64 128 256), losses := [] }

theorem u16706 : Upper (D 7) (R 7) [12,96,18,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16707 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 22 41 336 34 193 129 385), lower := (rows 13 98 22 41 336 34 64 128 256), losses := [] }

theorem u16707 : Upper (D 7) (R 7) [12,96,18,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16708 : Route 9 := (fun mask => (mask,id))

def c16708 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16708 : Upper (D 7) (R 7) [12,96,18,33,320,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,33,320,128] 13 (by decide) (choices 1) [1,2,128] r16708 c16708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3868
  · exact u3869
  · exact u3870

def b16709 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 41, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(3,1)], upper := (rows 13 98 22 41 400 33 194 194 450), lower := (rows 13 98 22 41 400 33 64 128 256), losses := [] }

theorem u16709 : Upper (D 7) (R 7) [12,96,18,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16710 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 98 22 41 400 34 193 193 449), lower := (rows 13 98 22 41 400 34 64 128 256), losses := [] }

theorem u16710 : Upper (D 7) (R 7) [12,96,18,33,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16711 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 41 400 96 195 131 387), lower := (rows 13 98 22 41 400 96 64 128 256), losses := [] }

theorem u16711 : Upper (D 7) (R 7) [12,96,18,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16712 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 66, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,1)], upper := (rows 13 98 22 41 400 160 67 195 323), lower := (rows 13 98 22 41 400 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 176 64 128 256), good := (rows 13 96 61 41 432 160 64 160 256) },{ target := 6, region := (rows 5 2 4 12 16 176 0 128 256), good := (rows 13 34 63 41 432 160 0 160 256) }] }

theorem u16712 : Upper (D 7) (R 7) [12,96,18,33,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16713 : PairBound 9 := { available := 322, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(1,0),(2,0),(4,0)], upper := (rows 13 98 22 137 176 33 322 450 322), lower := (rows 13 98 22 137 176 33 64 128 256), losses := [] }

theorem u16713 : Upper (D 7) (R 7) [12,96,18,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16714 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 22 137 176 34 321 449 321), lower := (rows 13 98 22 137 176 34 64 128 256), losses := [] }

theorem u16714 : Upper (D 7) (R 7) [12,96,18,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16715 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 137 176 96 323 387 259), lower := (rows 13 98 22 137 176 96 64 128 256), losses := [] }

theorem u16715 : Upper (D 7) (R 7) [12,96,18,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16716 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 354, targets := 128 }], pairs := [(0,5),(1,7),(3,5)], upper := (rows 13 98 22 137 176 288 67 195 323), lower := (rows 13 98 22 137 176 288 64 128 256), losses := [] }

theorem u16716 : Upper (D 7) (R 7) [12,96,18,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16716 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16717 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,0)], upper := (rows 13 98 22 137 273 34 224 224 480), lower := (rows 13 98 22 137 273 34 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 20 32 98 162 290), good := (rows 29 480 477 137 273 480 64 128 256) }] }

theorem u16717 : Upper (D 7) (R 7) [12,96,18,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16718 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 137 273 96 226 162 418), lower := (rows 13 98 22 137 273 96 64 128 256), losses := [] }

theorem u16718 : Upper (D 7) (R 7) [12,96,18,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16719_2 : Upper (D 7) (R 7) [12,96,18,129,257,128,2] 13 :=
  permutation_upper _ _ _ [12,96,18,129,257,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3871

theorem m16719_32 : Upper (D 7) (R 7) [12,96,18,129,257,128,32] 13 :=
  permutation_upper _ _ _ [12,96,18,129,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3872

def r16719 : Route 9 := (fun mask => (mask,id))

def c16719 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16719 : Upper (D 7) (R 7) [12,96,18,129,257,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,129,257,128] 13 (by decide) (choices 1) [2,32] r16719 c16719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16719_2
  · exact m16719_32

def b16720 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(1,0),(2,0),(4,0)], upper := (rows 13 98 22 137 304 33 194 194 450), lower := (rows 13 98 22 137 304 33 64 128 256), losses := [] }

theorem u16720 : Upper (D 7) (R 7) [12,96,18,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16721 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 22 137 304 34 193 193 449), lower := (rows 13 98 22 137 304 34 64 128 256), losses := [] }

theorem u16721 : Upper (D 7) (R 7) [12,96,18,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16722 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 137 304 96 195 131 387), lower := (rows 13 98 22 137 304 96 64 128 256), losses := [] }

theorem u16722 : Upper (D 7) (R 7) [12,96,18,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16723 : Route 9 := (fun mask => (mask,id))

def c16723 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16723 : Upper (D 7) (R 7) [12,96,18,129,288,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,129,288,128] 13 (by decide) (choices 1) [1,2] r16723 c16723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3873
  · exact u3874

def b16724 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 13 98 22 137 400 33 98 226 354), lower := (rows 13 98 22 137 400 33 64 128 256), losses := [] }

theorem u16724 : Upper (D 7) (R 7) [12,96,18,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16725_1 : Upper (D 7) (R 7) [12,96,18,129,384,2,1] 13 :=
  permutation_upper _ _ _ [12,96,18,129,384,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3875

def r16725 : Route 9 := (fun mask => (mask,id))

def c16725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16725 : Upper (D 7) (R 7) [12,96,18,129,384,2] 13 := by
  apply FastRouting.sound _ _ [12,96,18,129,384,2] 13 (by decide) (choices 1) [1,32] r16725 c16725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16725_1
  · exact u3876

def b16726 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 137 400 96 99 163 291), lower := (rows 13 98 22 137 400 96 64 128 256), losses := [] }

theorem u16726 : Upper (D 7) (R 7) [12,96,18,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16727 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 22 138 49 33 448 448 448), lower := (rows 13 98 22 138 49 33 64 128 256), losses := [] }

theorem u16727 : Upper (D 7) (R 7) [12,96,18,130,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16728 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 138 49 96 449 385 385), lower := (rows 13 98 22 138 49 96 64 128 256), losses := [] }

theorem u16728 : Upper (D 7) (R 7) [12,96,18,130,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16729 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(0,6),(2,6),(4,6)], upper := (rows 13 98 22 138 49 160 321 449 321), lower := (rows 13 98 22 138 49 160 64 128 256), losses := [] }

theorem u16729 : Upper (D 7) (R 7) [12,96,18,130,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16730 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 13 98 22 138 49 288 193 193 449), lower := (rows 13 98 22 138 49 288 64 128 256), losses := [] }

theorem u16730 : Upper (D 7) (R 7) [12,96,18,130,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16730 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16731 : Route 9 := (fun mask => (mask,id))

def c16731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16731 : Upper (D 7) (R 7) [12,96,18,130,257,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,257,1] 13 (by decide) (choices 1) [32,128] r16731 c16731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3877
  · exact u3878

def b16732 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 138 273 96 225 161 417), lower := (rows 13 98 22 138 273 96 64 128 256), losses := [] }

theorem u16732 : Upper (D 7) (R 7) [12,96,18,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16733_1 : Upper (D 7) (R 7) [12,96,18,130,257,128,1] 13 :=
  permutation_upper _ _ _ [12,96,18,130,257,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3878

theorem m16733_32 : Upper (D 7) (R 7) [12,96,18,130,257,128,32] 13 :=
  permutation_upper _ _ _ [12,96,18,130,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3879

def r16733 : Route 9 := (fun mask => (mask,id))

def c16733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16733 : Upper (D 7) (R 7) [12,96,18,130,257,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,257,128] 13 (by decide) (choices 1) [1,32] r16733 c16733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16733_1
  · exact m16733_32

def r16734 : Route 9 := (fun mask => (mask,id))

def c16734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16734 : Upper (D 7) (R 7) [12,96,18,130,288,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,288,1] 13 (by decide) (choices 1) [1,128] r16734 c16734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3880
  · exact u3881

def b16735 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 138 304 96 193 129 385), lower := (rows 13 98 22 138 304 96 64 128 256), losses := [] }

theorem u16735 : Upper (D 7) (R 7) [12,96,18,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16736 : Route 9 := (fun mask => (mask,id))

def c16736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16736 : Upper (D 7) (R 7) [12,96,18,130,288,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,288,128] 13 (by decide) (choices 1) [1] r16736 c16736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u3882

def r16737 : Route 9 := (fun mask => (mask,id))

def c16737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16737 : Upper (D 7) (R 7) [12,96,18,130,384,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,130,384,1] 13 (by decide) (choices 1) [1,32] r16737 c16737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3883
  · exact u3884

def b16738 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 138 400 96 97 161 289), lower := (rows 13 98 22 138 400 96 64 128 256), losses := [] }

theorem u16738 : Upper (D 7) (R 7) [12,96,18,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16739 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 38, targets := 128 }], pairs := [(0,6),(1,7),(2,7),(3,6)], upper := (rows 13 98 22 168 81 33 450 386 386), lower := (rows 13 98 22 168 81 33 64 128 256), losses := [] }

theorem u16739 : Upper (D 7) (R 7) [12,96,18,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16739
end Delivery.IrregularNine14.P07
