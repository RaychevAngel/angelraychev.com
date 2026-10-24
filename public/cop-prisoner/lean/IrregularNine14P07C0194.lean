import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0014

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11640 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 386 38 76 145 48 72 131 259), lower := (rows 97 386 38 76 145 48 72 128 256), losses := [] }

theorem u11640 : Upper (D 7) (R 7) [96,384,34,68,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11640 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11641 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 402, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(4,0)], upper := (rows 97 386 38 76 152 33 65 146 274), lower := (rows 97 386 38 76 152 33 65 128 256), losses := [] }

theorem u11641 : Upper (D 7) (R 7) [96,384,34,68,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11642 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 109, targets := 128 },{ cop := 2, region := 72, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 97 386 38 76 152 33 66 145 273), lower := (rows 97 386 38 76 152 33 66 128 256), losses := [] }

theorem u11642 : Upper (D 7) (R 7) [96,384,34,68,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11643 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 97 386 38 76 152 33 80 131 259), lower := (rows 97 386 38 76 152 33 80 128 256), losses := [] }

theorem u11643 : Upper (D 7) (R 7) [96,384,34,68,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11643 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11644 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 386 38 88 148 33 65 138 266), lower := (rows 97 386 38 88 148 33 65 128 256), losses := [] }

theorem u11644 : Upper (D 7) (R 7) [96,384,34,80,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11645 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,0)], upper := (rows 97 386 38 88 148 33 66 137 265), lower := (rows 97 386 38 88 148 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 70 128 256), good := (rows 96 450 102 88 220 32 66 128 256) }] }

theorem u11645 : Upper (D 7) (R 7) [96,384,34,80,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11646 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 105, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 386 38 88 148 33 72 131 259), lower := (rows 97 386 38 88 148 33 72 128 256), losses := [] }

theorem u11646 : Upper (D 7) (R 7) [96,384,34,80,132,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11646 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11647 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 386 44 88 145 34 65 134 262), lower := (rows 97 386 44 88 145 34 65 128 256), losses := [] }

theorem u11647 : Upper (D 7) (R 7) [96,384,40,80,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11648 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 386 44 88 145 34 66 133 261), lower := (rows 97 386 44 88 145 34 66 128 256), losses := [] }

theorem u11648 : Upper (D 7) (R 7) [96,384,40,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11649 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 386 44 88 145 34 68 131 259), lower := (rows 97 386 44 88 145 34 68 128 256), losses := [] }

theorem u11649 : Upper (D 7) (R 7) [96,384,40,80,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11649 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11650 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 0, region := 386, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(0,7),(1,5),(1,6)], upper := (rows 97 386 44 88 148 34 65 131 259), lower := (rows 97 386 44 88 148 34 65 128 256), losses := [] }

theorem u11650 : Upper (D 7) (R 7) [96,384,40,80,132,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11651 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 1, region := 124, targets := 1 }], pairs := [(2,0),(2,1),(3,1),(4,1)], upper := (rows 97 386 44 88 148 34 66 129 257), lower := (rows 97 386 44 88 148 34 66 128 256), losses := [] }

theorem u11651 : Upper (D 7) (R 7) [96,384,40,80,132,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11652 : PairBound 9 := { available := 448, camps := [{ cop := 5, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 21 104 176 34 448 448 448), lower := (rows 7 11 21 104 176 34 64 128 256), losses := [] }

theorem u11652 : Upper (D 7) (R 7) [6,9,17,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11653 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 11 21 104 176 96 450 386 386), lower := (rows 7 11 21 104 176 96 64 128 256), losses := [] }

theorem u11653 : Upper (D 7) (R 7) [6,9,17,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11654 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 21 104 176 160 322 450 322), lower := (rows 7 11 21 104 176 160 64 128 256), losses := [] }

theorem u11654 : Upper (D 7) (R 7) [6,9,17,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11655 : Route 9 := (fun mask => (mask,id))

def c11655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11655 : Upper (D 7) (R 7) [6,9,17,96,160,256] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,160,256] 13 (by decide) (choices 1) [2,128] r11655 c11655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u859
  · exact u860

def b11656 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 21 104 304 34 192 192 448), lower := (rows 7 11 21 104 304 34 64 128 256), losses := [] }

theorem u11656 : Upper (D 7) (R 7) [6,9,17,96,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11657 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 11 21 104 304 96 194 130 386), lower := (rows 7 11 21 104 304 96 64 128 256), losses := [] }

theorem u11657 : Upper (D 7) (R 7) [6,9,17,96,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11658 : Route 9 := (fun mask => (mask,id))

def c11658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11658 : Upper (D 7) (R 7) [6,9,17,96,288,128] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,288,128] 13 (by decide) (choices 1) [2,128] r11658 c11658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u861
  · exact u862

def b11659 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 21 104 400 34 224 224 480), lower := (rows 7 11 21 104 400 34 64 128 256), losses := [] }

theorem u11659 : Upper (D 7) (R 7) [6,9,17,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11660 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 11 21 104 400 96 226 162 418), lower := (rows 7 11 21 104 400 96 64 128 256), losses := [] }

theorem u11660 : Upper (D 7) (R 7) [6,9,17,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m11661_2 : Upper (D 7) (R 7) [6,9,17,96,384,128,2] 13 :=
  permutation_upper _ _ _ [6,9,17,96,384,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u863

theorem m11661_32 : Upper (D 7) (R 7) [6,9,17,96,384,128,32] 13 :=
  permutation_upper _ _ _ [6,9,17,96,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u864

def r11661 : Route 9 := (fun mask => (mask,id))

def c11661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11661 : Upper (D 7) (R 7) [6,9,17,96,384,128] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,384,128] 13 (by decide) (choices 1) [2,32] r11661 c11661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11661_2
  · exact m11661_32

def b11662 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 21 296 112 34 192 192 448), lower := (rows 7 11 21 296 112 34 64 128 256), losses := [] }

theorem u11662 : Upper (D 7) (R 7) [6,9,17,288,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11663 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 11 21 296 112 96 194 130 386), lower := (rows 7 11 21 296 112 96 64 128 256), losses := [] }

theorem u11663 : Upper (D 7) (R 7) [6,9,17,288,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11664 : Route 9 := (fun mask => (mask,id))

def c11664 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11664 : Upper (D 7) (R 7) [6,9,17,288,96,128] 13 := by
  apply FastRouting.sound _ _ [6,9,17,288,96,128] 13 (by decide) (choices 1) [2,128] r11664 c11664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u865
  · exact u866

def b11665 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 21 296 208 34 224 224 480), lower := (rows 7 11 21 296 208 34 64 128 256), losses := [] }

theorem u11665 : Upper (D 7) (R 7) [6,9,17,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11666 : Route 9 := (fun mask => (mask,id))

def c11666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11666 : Upper (D 7) (R 7) [6,9,17,288,192,64] 13 := by
  apply FastRouting.sound _ _ [6,9,17,288,192,64] 13 (by decide) (choices 1) [2,32,128] r11666 c11666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u867
  · exact u868
  · exact u869

def b11667 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 88 176 34 448 448 448), lower := (rows 7 11 37 88 176 34 64 128 256), losses := [] }

theorem u11667 : Upper (D 7) (R 7) [6,9,33,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11668 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 11 37 88 176 96 450 386 386), lower := (rows 7 11 37 88 176 96 64 128 256), losses := [] }

theorem u11668 : Upper (D 7) (R 7) [6,9,33,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11669 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 37 88 176 160 322 450 322), lower := (rows 7 11 37 88 176 160 64 128 256), losses := [] }

theorem u11669 : Upper (D 7) (R 7) [6,9,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11670 : Route 9 := (fun mask => (mask,id))

def c11670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11670 : Upper (D 7) (R 7) [6,9,33,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,160,256] 13 (by decide) (choices 1) [2,128] r11670 c11670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u870
  · exact u871

def b11671 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 88 304 34 192 192 448), lower := (rows 7 11 37 88 304 34 64 128 256), losses := [] }

theorem u11671 : Upper (D 7) (R 7) [6,9,33,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11672 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 11 37 88 304 96 194 130 386), lower := (rows 7 11 37 88 304 96 64 128 256), losses := [] }

theorem u11672 : Upper (D 7) (R 7) [6,9,33,80,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11673 : Route 9 := (fun mask => (mask,id))

def c11673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11673 : Upper (D 7) (R 7) [6,9,33,80,288,128] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,288,128] 13 (by decide) (choices 1) [2,128] r11673 c11673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u872
  · exact u873

def b11674 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 88 400 34 224 224 480), lower := (rows 7 11 37 88 400 34 64 128 256), losses := [] }

theorem u11674 : Upper (D 7) (R 7) [6,9,33,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11675 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 11 37 88 400 96 226 162 418), lower := (rows 7 11 37 88 400 96 64 128 256), losses := [] }

theorem u11675 : Upper (D 7) (R 7) [6,9,33,80,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11676 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 7 11 37 88 400 160 98 226 354), lower := (rows 7 11 37 88 400 160 64 128 256), losses := [{ target := 6, region := (rows 11 10 12 8 16 176 0 128 256), good := (rows 7 15 37 63 432 160 0 160 256) }] }

theorem u11676 : Upper (D 7) (R 7) [6,9,33,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11677 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 37 200 112 34 464 400 400), lower := (rows 7 11 37 200 112 34 64 128 256), losses := [] }

theorem u11677 : Upper (D 7) (R 7) [6,9,33,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11678 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 37 200 112 48 450 386 386), lower := (rows 7 11 37 200 112 48 64 128 256), losses := [] }

theorem u11678 : Upper (D 7) (R 7) [6,9,33,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11678 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11679 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 64 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 11 37 200 112 160 338 402 274), lower := (rows 7 11 37 200 112 160 64 128 256), losses := [] }

theorem u11679 : Upper (D 7) (R 7) [6,9,33,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11680 : Route 9 := (fun mask => (mask,id))

def c11680 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11680 : Upper (D 7) (R 7) [6,9,33,192,96,256] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,96,256] 13 (by decide) (choices 1) [2,16,128] r11680 c11680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u874
  · exact u875
  · exact u876

def b11681 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 11 37 200 274 48 224 224 480), lower := (rows 7 11 37 200 274 48 64 128 256), losses := [] }

theorem u11681 : Upper (D 7) (R 7) [6,9,33,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11681 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11682 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 11 37 200 274 96 240 176 432), lower := (rows 7 11 37 200 274 96 64 128 256), losses := [] }

theorem u11682 : Upper (D 7) (R 7) [6,9,33,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11683 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 200 304 34 208 208 464), lower := (rows 7 11 37 200 304 34 64 128 256), losses := [] }

theorem u11683 : Upper (D 7) (R 7) [6,9,33,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11684 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 37 200 304 48 194 194 450), lower := (rows 7 11 37 200 304 48 64 128 256), losses := [] }

theorem u11684 : Upper (D 7) (R 7) [6,9,33,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11684 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11685 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 11 37 200 304 96 210 146 402), lower := (rows 7 11 37 200 304 96 64 128 256), losses := [] }

theorem u11685 : Upper (D 7) (R 7) [6,9,33,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11686 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 200 336 34 240 176 432), lower := (rows 7 11 37 200 336 34 64 128 256), losses := [] }

theorem u11686 : Upper (D 7) (R 7) [6,9,33,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11687 : Route 9 := (fun mask => (mask,id))

def c11687 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11687 : Upper (D 7) (R 7) [6,9,33,192,320,16] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,320,16] 13 (by decide) (choices 1) [2,32,128] r11687 c11687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u877
  · exact u878
  · exact u879

def b11688 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 39, targets := 64 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 11 37 200 336 160 114 178 306), lower := (rows 7 11 37 200 336 160 64 128 256), losses := [] }

theorem u11688 : Upper (D 7) (R 7) [6,9,33,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11689 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 280 112 34 192 192 448), lower := (rows 7 11 37 280 112 34 64 128 256), losses := [] }

theorem u11689 : Upper (D 7) (R 7) [6,9,33,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11690 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 11 37 280 112 96 194 130 386), lower := (rows 7 11 37 280 112 96 64 128 256), losses := [] }

theorem u11690 : Upper (D 7) (R 7) [6,9,33,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11691 : Route 9 := (fun mask => (mask,id))

def c11691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11691 : Upper (D 7) (R 7) [6,9,33,272,96,128] 13 := by
  apply FastRouting.sound _ _ [6,9,33,272,96,128] 13 (by decide) (choices 1) [2,128] r11691 c11691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u880
  · exact u881

def b11692 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 37 280 208 34 224 224 480), lower := (rows 7 11 37 280 208 34 64 128 256), losses := [] }

theorem u11692 : Upper (D 7) (R 7) [6,9,33,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11693 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 7 11 37 280 208 96 226 162 418), lower := (rows 7 11 37 280 208 96 64 128 256), losses := [{ target := 7, region := (rows 11 10 12 8 16 112 64 0 256), good := (rows 7 15 37 319 112 96 96 0 256) }] }

theorem u11693 : Upper (D 7) (R 7) [6,9,33,272,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11694 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 37 328 112 34 208 144 400), lower := (rows 7 11 37 328 112 34 64 128 256), losses := [] }

theorem u11694 : Upper (D 7) (R 7) [6,9,33,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11695 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 37 328 112 48 194 130 386), lower := (rows 7 11 37 328 112 48 64 128 256), losses := [] }

theorem u11695 : Upper (D 7) (R 7) [6,9,33,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11695 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11696 : Route 9 := (fun mask => (mask,id))

def c11696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11696 : Upper (D 7) (R 7) [6,9,33,320,96,128] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,96,128] 13 (by decide) (choices 1) [2,16,128] r11696 c11696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u882
  · exact u883
  · exact u884

def b11697 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 11 37 328 146 48 224 224 480), lower := (rows 7 11 37 328 146 48 64 128 256), losses := [] }

theorem u11697 : Upper (D 7) (R 7) [6,9,33,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11697 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11698 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 11 37 328 146 96 240 176 432), lower := (rows 7 11 37 328 146 96 64 128 256), losses := [] }

theorem u11698 : Upper (D 7) (R 7) [6,9,33,320,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11699 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 7 11 37 328 146 160 112 240 368), lower := (rows 7 11 37 328 146 160 64 128 256), losses := [] }

theorem u11699 : Upper (D 7) (R 7) [6,9,33,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11699
end Delivery.IrregularNine14.P07
