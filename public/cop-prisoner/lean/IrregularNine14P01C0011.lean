import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0000

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b660 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 69 138 48 160 92 156 284), lower := (rows 51 322 69 138 48 160 64 128 256), losses := [] }

theorem u660 : Upper (D 1) (R 1) [50,320,65,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b660
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 69 140 18 160 120 184 312), lower := (rows 51 322 69 140 18 160 64 128 256), losses := [] }

theorem u661 : Upper (D 1) (R 1) [50,320,65,132,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b661
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 51 322 69 140 24 160 114 178 306), lower := (rows 51 322 69 140 24 160 64 128 256), losses := [] }

theorem u662 : Upper (D 1) (R 1) [50,320,65,132,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b662
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 69 140 48 160 90 154 282), lower := (rows 51 322 69 140 48 160 64 128 256), losses := [] }

theorem u663 : Upper (D 1) (R 1) [50,320,65,132,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b663
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 76 137 18 160 116 180 308), lower := (rows 51 322 76 137 18 160 64 128 256), losses := [] }

theorem u664 : Upper (D 1) (R 1) [50,320,72,129,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b664
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 51 322 76 137 20 160 114 178 306), lower := (rows 51 322 76 137 20 160 64 128 256), losses := [] }

theorem u665 : Upper (D 1) (R 1) [50,320,72,129,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b665
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 76 137 48 160 86 150 278), lower := (rows 51 322 76 137 48 160 64 128 256), losses := [] }

theorem u666 : Upper (D 1) (R 1) [50,320,72,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b666
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 51 322 76 138 17 160 116 180 308), lower := (rows 51 322 76 138 17 160 64 128 256), losses := [] }

theorem u667 : Upper (D 1) (R 1) [50,320,72,130,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b667
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 322 76 138 20 160 113 177 305), lower := (rows 51 322 76 138 20 160 64 128 256), losses := [] }

theorem u668 : Upper (D 1) (R 1) [50,320,72,130,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b668
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b669 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 76 138 48 160 85 149 277), lower := (rows 51 322 76 138 48 160 64 128 256), losses := [] }

theorem u669 : Upper (D 1) (R 1) [50,320,72,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b669
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b670 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 84 137 144 34 108 172 300), lower := (rows 51 322 84 137 144 34 64 128 256), losses := [] }

theorem u670 : Upper (D 1) (R 1) [50,320,80,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b670
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 51 322 84 137 144 36 106 170 298), lower := (rows 51 322 84 137 144 36 64 128 256), losses := [] }

theorem u671 : Upper (D 1) (R 1) [50,320,80,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b671
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b672 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 51 322 84 137 144 40 102 166 294), lower := (rows 51 322 84 137 144 40 64 128 256), losses := [] }

theorem u672 : Upper (D 1) (R 1) [50,320,80,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b672
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 51 322 84 138 144 33 108 172 300), lower := (rows 51 322 84 138 144 33 64 128 256), losses := [] }

theorem u673 : Upper (D 1) (R 1) [50,320,80,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b673
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 51 322 84 138 144 36 105 169 297), lower := (rows 51 322 84 138 144 36 64 128 256), losses := [] }

theorem u674 : Upper (D 1) (R 1) [50,320,80,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b674
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 322 84 138 144 40 101 165 293), lower := (rows 51 322 84 138 144 40 64 128 256), losses := [] }

theorem u675 : Upper (D 1) (R 1) [50,320,80,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b675
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 51 322 84 140 144 33 106 170 298), lower := (rows 51 322 84 140 144 33 64 128 256), losses := [] }

theorem u676 : Upper (D 1) (R 1) [50,320,80,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b676
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b677 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 84 140 144 34 105 169 297), lower := (rows 51 322 84 140 144 34 64 128 256), losses := [] }

theorem u677 : Upper (D 1) (R 1) [50,320,80,132,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b677
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b678 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 51 322 84 140 144 40 99 163 291), lower := (rows 51 322 84 140 144 40 64 128 256), losses := [] }

theorem u678 : Upper (D 1) (R 1) [50,320,80,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b678
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b679 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 51 322 84 168 144 33 78 142 270), lower := (rows 51 322 84 168 144 33 64 128 256), losses := [] }

theorem u679 : Upper (D 1) (R 1) [50,320,80,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b679
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b680 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 84 168 144 34 77 141 269), lower := (rows 51 322 84 168 144 34 64 128 256), losses := [] }

theorem u680 : Upper (D 1) (R 1) [50,320,80,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b680
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b681 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 51 322 84 168 144 36 75 139 267), lower := (rows 51 322 84 168 144 36 64 128 256), losses := [] }

theorem u681 : Upper (D 1) (R 1) [50,320,80,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b681
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b682 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 51 322 84 168 144 40 71 135 263), lower := (rows 51 322 84 168 144 40 64 128 256), losses := [] }

theorem u682 : Upper (D 1) (R 1) [50,320,80,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b682
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b683 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 11 70 392 18 160 112 240 368), lower := (rows 53 11 70 392 18 160 64 128 256), losses := [] }

theorem u683 : Upper (D 1) (R 1) [52,9,66,384,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b683
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b684 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 70 392 48 160 82 210 338), lower := (rows 53 11 70 392 48 160 64 128 256), losses := [] }

theorem u684 : Upper (D 1) (R 1) [52,9,66,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b684
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 11 70 392 80 160 114 178 306), lower := (rows 53 11 70 392 80 160 64 128 256), losses := [] }

theorem u685 : Upper (D 1) (R 1) [52,9,66,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b685
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 53 11 196 328 18 34 240 176 432), lower := (rows 53 11 196 328 18 34 64 128 256), losses := [] }

theorem u686 : Upper (D 1) (R 1) [52,9,192,320,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b686
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 11 196 328 18 48 226 162 418), lower := (rows 53 11 196 328 18 48 64 128 256), losses := [] }

theorem u687 : Upper (D 1) (R 1) [52,9,192,320,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b687
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b688 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 11 196 328 18 160 114 178 306), lower := (rows 53 11 196 328 18 160 64 128 256), losses := [] }

theorem u688 : Upper (D 1) (R 1) [52,9,192,320,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b688
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b689 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 11 262 200 18 96 240 176 432), lower := (rows 53 11 262 200 18 96 64 128 256), losses := [] }

theorem u689 : Upper (D 1) (R 1) [52,9,258,192,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b689
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b690 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 262 200 48 96 210 146 402), lower := (rows 53 11 262 200 48 96 64 128 256), losses := [] }

theorem u690 : Upper (D 1) (R 1) [52,9,258,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b690
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r691 : Route 9 := (fun mask => (mask,id))

def c691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u691 : Upper (D 1) (R 1) [52,9,258,192,64,128] 13 := by
  apply FastRouting.sound _ _ [52,9,258,192,64,128] 13 (by decide) (choices 1) [2,16,32] r691 c691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u44
  · exact u45
  · exact u46

def b692 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 11 324 74 18 160 240 176 432), lower := (rows 53 11 324 74 18 160 64 128 256), losses := [] }

theorem u692 : Upper (D 1) (R 1) [52,9,320,66,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b692
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b693 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 324 74 48 160 210 146 402), lower := (rows 53 11 324 74 48 160 64 128 256), losses := [] }

theorem u693 : Upper (D 1) (R 1) [52,9,320,66,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b693
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 11 324 74 144 160 114 178 306), lower := (rows 53 11 324 74 144 160 64 128 256), losses := [] }

theorem u694 : Upper (D 1) (R 1) [52,9,320,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b694
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b695 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 11 324 138 18 160 112 240 368), lower := (rows 53 11 324 138 18 160 64 128 256), losses := [] }

theorem u695 : Upper (D 1) (R 1) [52,9,320,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b695
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b696 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 324 138 48 160 82 210 338), lower := (rows 53 11 324 138 48 160 64 128 256), losses := [] }

theorem u696 : Upper (D 1) (R 1) [52,9,320,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b696
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b697 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 138, targets := 64 }], pairs := [(1,6)], upper := (rows 53 11 324 138 80 160 114 178 306), lower := (rows 53 11 324 138 80 160 64 128 256), losses := [] }

theorem u697 : Upper (D 1) (R 1) [52,9,320,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b697
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b698 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1)], upper := (rows 53 11 324 200 18 34 240 176 432), lower := (rows 53 11 324 200 18 34 64 128 256), losses := [] }

theorem u698 : Upper (D 1) (R 1) [52,9,320,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b698
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b699 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 53 11 324 200 18 48 226 162 418), lower := (rows 53 11 324 200 18 48 64 128 256), losses := [] }

theorem u699 : Upper (D 1) (R 1) [52,9,320,192,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b699
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r700 : Route 9 := (fun mask => (mask,id))

def c700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u700 : Upper (D 1) (R 1) [52,9,320,192,2,128] 13 := by
  apply FastRouting.sound _ _ [52,9,320,192,2,128] 13 (by decide) (choices 1) [2,16,32] r700 c700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u47
  · exact u48
  · exact u49

def b701 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 324 200 48 160 82 146 274), lower := (rows 53 11 324 200 48 160 64 128 256), losses := [] }

theorem u701 : Upper (D 1) (R 1) [52,9,320,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b701
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b702 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 53 26 70 296 144 33 194 194 450), lower := (rows 53 26 70 296 144 33 64 128 256), losses := [] }

theorem u702 : Upper (D 1) (R 1) [52,24,66,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b702
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b703 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 26 70 296 144 34 193 193 449), lower := (rows 53 26 70 296 144 34 64 128 256), losses := [] }

theorem u703 : Upper (D 1) (R 1) [52,24,66,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b703
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 70 296 144 96 195 131 387), lower := (rows 53 26 70 296 144 96 64 128 256), losses := [] }

theorem u704 : Upper (D 1) (R 1) [52,24,66,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b704
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 26 70 296 144 160 67 195 323), lower := (rows 53 26 70 296 144 160 64 128 256), losses := [] }

theorem u705 : Upper (D 1) (R 1) [52,24,66,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b705
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 53 26 262 104 144 33 194 194 450), lower := (rows 53 26 262 104 144 33 64 128 256), losses := [] }

theorem u706 : Upper (D 1) (R 1) [52,24,258,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b706
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 26 262 104 144 34 193 193 449), lower := (rows 53 26 262 104 144 34 64 128 256), losses := [] }

theorem u707 : Upper (D 1) (R 1) [52,24,258,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b707
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 53 26 262 104 144 96 195 131 387), lower := (rows 53 26 262 104 144 96 64 128 256), losses := [] }

theorem u708 : Upper (D 1) (R 1) [52,24,258,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b708
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 26 262 104 144 160 67 195 323), lower := (rows 53 26 262 104 144 160 64 128 256), losses := [] }

theorem u709 : Upper (D 1) (R 1) [52,24,258,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b709
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 26 324 74 144 33 226 162 418), lower := (rows 53 26 324 74 144 33 64 128 256), losses := [] }

theorem u710 : Upper (D 1) (R 1) [52,24,320,66,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b710
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 469, targets := 2 }], pairs := [(0,1)], upper := (rows 53 26 324 74 144 34 225 161 417), lower := (rows 53 26 324 74 144 34 64 128 256), losses := [] }

theorem u711 : Upper (D 1) (R 1) [52,24,320,66,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b711
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 26 324 74 144 160 99 163 291), lower := (rows 53 26 324 74 144 160 64 128 256), losses := [] }

theorem u712 : Upper (D 1) (R 1) [52,24,320,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b712
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b713 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 53 26 324 104 144 33 194 130 386), lower := (rows 53 26 324 104 144 33 64 128 256), losses := [] }

theorem u713 : Upper (D 1) (R 1) [52,24,320,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b713
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r714 : Route 9 := (fun mask => (mask,id))

def c714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u714 : Upper (D 1) (R 1) [52,24,320,96,128,2] 13 := by
  apply FastRouting.sound _ _ [52,24,320,96,128,2] 13 (by decide) (choices 1) [1,2,128] r714 c714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u50
  · exact u51
  · exact u52

def b715 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 26 324 104 144 160 67 131 259), lower := (rows 53 26 324 104 144 160 64 128 256), losses := [] }

theorem u715 : Upper (D 1) (R 1) [52,24,320,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b715
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 392, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 14 392 18 96 240 176 432), lower := (rows 53 67 14 392 18 96 64 128 256), losses := [] }

theorem u716 : Upper (D 1) (R 1) [52,65,10,384,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b716
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b717 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 14 392 48 96 210 146 402), lower := (rows 53 67 14 392 48 96 64 128 256), losses := [] }

theorem u717 : Upper (D 1) (R 1) [52,65,10,384,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b717
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b718 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 14 392 80 160 114 178 306), lower := (rows 53 67 14 392 80 160 64 128 256), losses := [] }

theorem u718 : Upper (D 1) (R 1) [52,65,10,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b718
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b719 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 53 67 134 266 24 96 240 176 432), lower := (rows 53 67 134 266 24 96 64 128 256), losses := [] }

theorem u719 : Upper (D 1) (R 1) [52,65,130,258,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b719
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P01
