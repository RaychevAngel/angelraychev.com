import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b660 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 304, targets := 4 }], pairs := [(4,2)], upper := (rows 7 67 140 44 49 288 72 146 274), lower := (rows 7 67 140 44 49 288 72 128 256), losses := [] }

theorem u660 : Upper (D 5) (R 5) [6,65,136,36,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b660
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 7 67 140 44 49 288 80 138 266), lower := (rows 7 67 140 44 49 288 80 128 256), losses := [] }

theorem u661 : Upper (D 5) (R 5) [6,65,136,36,33,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b661
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 44 50 288 65 152 280), lower := (rows 7 67 140 44 50 288 65 128 256), losses := [] }

theorem u662 : Upper (D 5) (R 5) [6,65,136,36,34,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b662
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 304, targets := 4 }], pairs := [(4,2)], upper := (rows 7 67 140 44 50 288 72 145 273), lower := (rows 7 67 140 44 50 288 72 128 256), losses := [] }

theorem u663 : Upper (D 5) (R 5) [6,65,136,36,34,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b663
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 67 140 44 50 288 80 137 265), lower := (rows 7 67 140 44 50 288 80 128 256), losses := [] }

theorem u664 : Upper (D 5) (R 5) [6,65,136,36,34,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b664
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 44 273 48 66 168 296), lower := (rows 7 67 140 44 273 48 66 128 256), losses := [] }

theorem u665 : Upper (D 5) (R 5) [6,65,136,36,257,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b665
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 304, targets := 4 }], pairs := [(4,2)], upper := (rows 7 67 140 44 273 48 72 162 290), lower := (rows 7 67 140 44 273 48 72 128 256), losses := [] }

theorem u666 : Upper (D 5) (R 5) [6,65,136,36,257,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b666
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 44 273 48 96 138 266), lower := (rows 7 67 140 44 273 48 96 128 256), losses := [] }

theorem u667 : Upper (D 5) (R 5) [6,65,136,36,257,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b667
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 44 274 48 65 168 296), lower := (rows 7 67 140 44 274 48 65 128 256), losses := [] }

theorem u668 : Upper (D 5) (R 5) [6,65,136,36,258,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b668
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b669 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 4 }], pairs := [(4,2)], upper := (rows 7 67 140 44 274 48 72 161 289), lower := (rows 7 67 140 44 274 48 72 128 256), losses := [] }

theorem u669 : Upper (D 5) (R 5) [6,65,136,36,258,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b669
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b670 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 44 274 48 96 137 265), lower := (rows 7 67 140 44 274 48 96 128 256), losses := [] }

theorem u670 : Upper (D 5) (R 5) [6,65,136,36,258,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b670
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 280 34 65 176 304), lower := (rows 7 67 140 44 280 34 65 128 256), losses := [] }

theorem u671 : Upper (D 5) (R 5) [6,65,136,36,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b671
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b672 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 140 44 280 34 80 161 289), lower := (rows 7 67 140 44 280 34 80 128 256), losses := [] }

theorem u672 : Upper (D 5) (R 5) [6,65,136,36,264,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b672
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 44 280 34 96 145 273), lower := (rows 7 67 140 44 280 34 96 128 256), losses := [] }

theorem u673 : Upper (D 5) (R 5) [6,65,136,36,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b673
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 304 33 66 152 280), lower := (rows 7 67 140 44 304 33 66 128 256), losses := [] }

theorem u674 : Upper (D 5) (R 5) [6,65,136,36,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b674
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 67 140 44 304 33 72 146 274), lower := (rows 7 67 140 44 304 33 72 128 256), losses := [] }

theorem u675 : Upper (D 5) (R 5) [6,65,136,36,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b675
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 7 67 140 44 304 33 80 138 266), lower := (rows 7 67 140 44 304 33 80 128 256), losses := [] }

theorem u676 : Upper (D 5) (R 5) [6,65,136,36,288,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b676
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b677 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 44 304 34 65 152 280), lower := (rows 7 67 140 44 304 34 65 128 256), losses := [] }

theorem u677 : Upper (D 5) (R 5) [6,65,136,36,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b677
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b678 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 67 140 44 304 34 72 145 273), lower := (rows 7 67 140 44 304 34 72 128 256), losses := [] }

theorem u678 : Upper (D 5) (R 5) [6,65,136,36,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b678
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b679 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 140 44 304 34 80 137 265), lower := (rows 7 67 140 44 304 34 80 128 256), losses := [] }

theorem u679 : Upper (D 5) (R 5) [6,65,136,36,288,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b679
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b680 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 172, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 56 274 36 65 168 296), lower := (rows 7 67 140 56 274 36 65 128 256), losses := [] }

theorem u680 : Upper (D 5) (R 5) [6,65,136,48,258,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b680
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b681 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 140 56 274 36 72 161 289), lower := (rows 7 67 140 56 274 36 72 128 256), losses := [] }

theorem u681 : Upper (D 5) (R 5) [6,65,136,48,258,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b681
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b682 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 56 274 36 96 137 265), lower := (rows 7 67 140 56 274 36 96 128 256), losses := [] }

theorem u682 : Upper (D 5) (R 5) [6,65,136,48,258,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b682
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b683 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 56 276 33 66 168 296), lower := (rows 7 67 140 56 276 33 66 128 256), losses := [] }

theorem u683 : Upper (D 5) (R 5) [6,65,136,48,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b683
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b684 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 140 56 276 33 72 162 290), lower := (rows 7 67 140 56 276 33 72 128 256), losses := [] }

theorem u684 : Upper (D 5) (R 5) [6,65,136,48,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b684
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 56 276 33 96 138 266), lower := (rows 7 67 140 56 276 33 96 128 256), losses := [] }

theorem u685 : Upper (D 5) (R 5) [6,65,136,48,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b685
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 56 276 34 65 168 296), lower := (rows 7 67 140 56 276 34 65 128 256), losses := [] }

theorem u686 : Upper (D 5) (R 5) [6,65,136,48,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b686
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 140 56 276 34 72 161 289), lower := (rows 7 67 140 56 276 34 72 128 256), losses := [] }

theorem u687 : Upper (D 5) (R 5) [6,65,136,48,260,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b687
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b688 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 56 276 34 96 137 265), lower := (rows 7 67 140 56 276 34 96 128 256), losses := [] }

theorem u688 : Upper (D 5) (R 5) [6,65,136,48,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b688
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b689 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 268 26 48 65 160 288), lower := (rows 7 67 140 268 26 48 65 128 256), losses := [] }

theorem u689 : Upper (D 5) (R 5) [6,65,136,260,10,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b689
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r690 : Route 9 := (fun mask => (mask,id))

def c690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u690 : Upper (D 5) (R 5) [6,65,136,260,10,16,32] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,10,16,32] 13 (by decide) (choices 1) [1,32] r690 c690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u40
  · exact u41

def b691 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 268 56 33 66 176 304), lower := (rows 7 67 140 268 56 33 66 128 256), losses := [] }

theorem u691 : Upper (D 5) (R 5) [6,65,136,260,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b691
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r692 : Route 9 := (fun mask => (mask,id))

def c692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u692 : Upper (D 5) (R 5) [6,65,136,260,40,1,16] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,40,1,16] 13 (by decide) (choices 1) [2,32] r692 c692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u42
  · exact u43

def b693 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 268 56 33 96 146 274), lower := (rows 7 67 140 268 56 33 96 128 256), losses := [] }

theorem u693 : Upper (D 5) (R 5) [6,65,136,260,40,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b693
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 268 56 34 65 176 304), lower := (rows 7 67 140 268 56 34 65 128 256), losses := [] }

theorem u694 : Upper (D 5) (R 5) [6,65,136,260,40,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b694
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r695 : Route 9 := (fun mask => (mask,id))

def c695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u695 : Upper (D 5) (R 5) [6,65,136,260,40,2,16] 13 := by
  apply FastRouting.sound _ _ [6,65,136,260,40,2,16] 13 (by decide) (choices 1) [1,32] r695 c695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u44
  · exact u45

def b696 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 268 56 34 96 145 273), lower := (rows 7 67 140 268 56 34 96 128 256), losses := [] }

theorem u696 : Upper (D 5) (R 5) [6,65,136,260,40,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b696
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b697 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 296 25 36 66 176 304), lower := (rows 7 67 140 296 25 36 66 128 256), losses := [] }

theorem u697 : Upper (D 5) (R 5) [6,65,136,288,9,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b697
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b698 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 296 25 36 80 162 290), lower := (rows 7 67 140 296 25 36 80 128 256), losses := [] }

theorem u698 : Upper (D 5) (R 5) [6,65,136,288,9,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b698
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b699 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 296 25 36 96 146 274), lower := (rows 7 67 140 296 25 36 96 128 256), losses := [] }

theorem u699 : Upper (D 5) (R 5) [6,65,136,288,9,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b699
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b700 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 296 25 48 66 164 292), lower := (rows 7 67 140 296 25 48 66 128 256), losses := [] }

theorem u700 : Upper (D 5) (R 5) [6,65,136,288,9,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b700
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 296 25 48 68 162 290), lower := (rows 7 67 140 296 25 48 68 128 256), losses := [] }

theorem u701 : Upper (D 5) (R 5) [6,65,136,288,9,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b701
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b702 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2)], upper := (rows 7 67 140 296 25 48 96 134 262), lower := (rows 7 67 140 296 25 48 96 128 256), losses := [] }

theorem u702 : Upper (D 5) (R 5) [6,65,136,288,9,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b702
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b703 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 296 26 36 65 176 304), lower := (rows 7 67 140 296 26 36 65 128 256), losses := [] }

theorem u703 : Upper (D 5) (R 5) [6,65,136,288,10,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b703
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 296 26 36 80 161 289), lower := (rows 7 67 140 296 26 36 80 128 256), losses := [] }

theorem u704 : Upper (D 5) (R 5) [6,65,136,288,10,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b704
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 296 26 36 96 145 273), lower := (rows 7 67 140 296 26 36 96 128 256), losses := [] }

theorem u705 : Upper (D 5) (R 5) [6,65,136,288,10,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b705
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 296 26 48 65 164 292), lower := (rows 7 67 140 296 26 48 65 128 256), losses := [] }

theorem u706 : Upper (D 5) (R 5) [6,65,136,288,10,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b706
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 296 26 48 68 161 289), lower := (rows 7 67 140 296 26 48 68 128 256), losses := [] }

theorem u707 : Upper (D 5) (R 5) [6,65,136,288,10,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b707
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 133, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 296 26 48 96 133 261), lower := (rows 7 67 140 296 26 48 96 128 256), losses := [] }

theorem u708 : Upper (D 5) (R 5) [6,65,136,288,10,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b708
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 42 280 36 65 168 296), lower := (rows 7 67 148 42 280 36 65 128 256), losses := [] }

theorem u709 : Upper (D 5) (R 5) [6,65,144,34,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b709
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(2,1),(3,0)], upper := (rows 7 67 148 42 280 36 72 161 289), lower := (rows 7 67 148 42 280 36 72 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 125 88 131 259), good := (rows 421 481 244 508 380 36 124 128 256) }] }

theorem u710 : Upper (D 5) (R 5) [6,65,144,34,264,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b710
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 67 148 42 280 36 96 137 265), lower := (rows 7 67 148 42 280 36 96 128 256), losses := [] }

theorem u711 : Upper (D 5) (R 5) [6,65,144,34,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b711
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 42 304 36 65 136 264), lower := (rows 7 67 148 42 304 36 65 128 256), losses := [] }

theorem u712 : Upper (D 5) (R 5) [6,65,144,34,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b712
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r713 : Route 9 := (fun mask => (mask,id))

def c713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u713 : Upper (D 5) (R 5) [6,65,144,34,288,4,8] 13 := by
  apply FastRouting.sound _ _ [6,65,144,34,288,4,8] 13 (by decide) (choices 1) [1,8] r713 c713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u46
  · exact u47

def b714 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 44 280 33 66 168 296), lower := (rows 7 67 148 44 280 33 66 128 256), losses := [] }

theorem u714 : Upper (D 5) (R 5) [6,65,144,36,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b714
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b715 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 148 44 280 33 72 162 290), lower := (rows 7 67 148 44 280 33 72 128 256), losses := [] }

theorem u715 : Upper (D 5) (R 5) [6,65,144,36,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b715
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 148 44 280 33 96 138 266), lower := (rows 7 67 148 44 280 33 96 128 256), losses := [] }

theorem u716 : Upper (D 5) (R 5) [6,65,144,36,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b716
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b717 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 44 280 34 65 168 296), lower := (rows 7 67 148 44 280 34 65 128 256), losses := [] }

theorem u717 : Upper (D 5) (R 5) [6,65,144,36,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b717
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b718 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 148 44 280 34 72 161 289), lower := (rows 7 67 148 44 280 34 72 128 256), losses := [] }

theorem u718 : Upper (D 5) (R 5) [6,65,144,36,264,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b718
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b719 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 148 44 280 34 96 137 265), lower := (rows 7 67 148 44 280 34 96 128 256), losses := [] }

theorem u719 : Upper (D 5) (R 5) [6,65,144,36,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b719
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P05
