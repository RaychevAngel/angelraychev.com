import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0001

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b660 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 7 35 324 137 176 48 73 201 329), lower := (rows 7 35 324 137 176 48 64 128 256), losses := [] }

theorem u660 : Upper (D 3) (R 3) [6,33,320,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b660
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 137 176 96 89 153 281), lower := (rows 7 35 324 137 176 96 64 128 256), losses := [] }

theorem u661 : Upper (D 3) (R 3) [6,33,320,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b661
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 137 208 33 120 184 312), lower := (rows 7 35 324 137 208 33 64 128 256), losses := [] }

theorem u662 : Upper (D 3) (R 3) [6,33,320,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b662
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 35 324 137 208 40 113 177 305), lower := (rows 7 35 324 137 208 40 64 128 256), losses := [] }

theorem u663 : Upper (D 3) (R 3) [6,33,320,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b663
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 35 324 137 208 48 105 169 297), lower := (rows 7 35 324 137 208 48 64 128 256), losses := [] }

theorem u664 : Upper (D 3) (R 3) [6,33,320,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b664
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 168 208 33 89 153 281), lower := (rows 7 35 324 168 208 33 64 128 256), losses := [] }

theorem u665 : Upper (D 3) (R 3) [6,33,320,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b665
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 35 324 168 208 40 81 145 273), lower := (rows 7 35 324 168 208 40 64 128 256), losses := [] }

theorem u666 : Upper (D 3) (R 3) [6,33,320,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b666
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 35 324 168 208 48 73 137 265), lower := (rows 7 35 324 168 208 48 64 128 256), losses := [] }

theorem u667 : Upper (D 3) (R 3) [6,33,320,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b667
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 84 137 273 33 224 224 480), lower := (rows 7 42 84 137 273 33 64 128 256), losses := [] }

theorem u668 : Upper (D 3) (R 3) [6,40,80,129,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b668
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r669 : Route 9 := (fun mask => (mask,id))

def c669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u669 : Upper (D 3) (R 3) [6,40,80,129,257,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257,64] 13 (by decide) (choices 1) [1,32,128] r669 c669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u80
  · exact u81
  · exact u82

def b670 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 84 137 273 160 97 225 353), lower := (rows 7 42 84 137 273 160 64 128 256), losses := [] }

theorem u670 : Upper (D 3) (R 3) [6,40,80,129,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b670
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 265 112 33 209 145 401), lower := (rows 7 42 196 265 112 33 64 128 256), losses := [] }

theorem u671 : Upper (D 3) (R 3) [6,40,192,257,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b671
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b672 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 196 265 112 48 193 129 385), lower := (rows 7 42 196 265 112 48 64 128 256), losses := [] }

theorem u672 : Upper (D 3) (R 3) [6,40,192,257,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b672
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 265 112 160 81 145 273), lower := (rows 7 42 196 265 112 160 64 128 256), losses := [] }

theorem u673 : Upper (D 3) (R 3) [6,40,192,257,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b673
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 261 25 208 33 224 224 480), lower := (rows 7 42 261 25 208 33 64 128 256), losses := [] }

theorem u674 : Upper (D 3) (R 3) [6,40,257,17,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b674
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 261 25 208 96 225 161 417), lower := (rows 7 42 261 25 208 96 64 128 256), losses := [] }

theorem u675 : Upper (D 3) (R 3) [6,40,257,17,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b675
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 7 42 261 73 112 33 208 144 400), lower := (rows 7 42 261 73 112 33 64 128 256), losses := [] }

theorem u676 : Upper (D 3) (R 3) [6,40,257,65,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b676
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b677 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 261 73 112 48 193 129 385), lower := (rows 7 42 261 73 112 48 64 128 256), losses := [] }

theorem u677 : Upper (D 3) (R 3) [6,40,257,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b677
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r678 : Route 9 := (fun mask => (mask,id))

def c678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u678 : Upper (D 3) (R 3) [6,40,257,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,96,128] 13 (by decide) (choices 1) [1,16,128] r678 c678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u83
  · exact u84
  · exact u85

def b679 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 7 42 261 73 145 48 224 224 480), lower := (rows 7 42 261 73 145 48 64 128 256), losses := [] }

theorem u679 : Upper (D 3) (R 3) [6,40,257,65,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b679
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b680 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 261 73 145 96 240 176 432), lower := (rows 7 42 261 73 145 96 64 128 256), losses := [] }

theorem u680 : Upper (D 3) (R 3) [6,40,257,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b680
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r681 : Route 9 := (fun mask => (mask,id))

def c681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u681 : Upper (D 3) (R 3) [6,40,257,65,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,129,128] 13 (by decide) (choices 1) [16,32] r681 c681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u86
  · exact u87

def b682 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 261 73 176 33 208 208 464), lower := (rows 7 42 261 73 176 33 64 128 256), losses := [] }

theorem u682 : Upper (D 3) (R 3) [6,40,257,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b682
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b683 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 42 261 73 176 48 193 193 449), lower := (rows 7 42 261 73 176 48 64 128 256), losses := [] }

theorem u683 : Upper (D 3) (R 3) [6,40,257,65,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b683
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b684 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 261 73 176 96 209 145 401), lower := (rows 7 42 261 73 176 96 64 128 256), losses := [] }

theorem u684 : Upper (D 3) (R 3) [6,40,257,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b684
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 261 73 176 160 81 209 337), lower := (rows 7 42 261 73 176 160 64 128 256), losses := [] }

theorem u685 : Upper (D 3) (R 3) [6,40,257,65,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b685
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 261 73 208 33 240 176 432), lower := (rows 7 42 261 73 208 33 64 128 256), losses := [] }

theorem u686 : Upper (D 3) (R 3) [6,40,257,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b686
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 42 261 73 208 48 225 161 417), lower := (rows 7 42 261 73 208 48 64 128 256), losses := [] }

theorem u687 : Upper (D 3) (R 3) [6,40,257,65,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b687
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r688 : Route 9 := (fun mask => (mask,id))

def c688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u688 : Upper (D 3) (R 3) [6,40,257,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,192,128] 13 (by decide) (choices 1) [1,16,32] r688 c688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u88
  · exact u89
  · exact u90

def b689 : PairBound 9 := { available := 224, camps := [], pairs := [(1,6)], upper := (rows 7 42 261 88 145 33 224 224 480), lower := (rows 7 42 261 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 53 0 128 256), good := (rows 39 42 293 58 177 33 0 128 256) }] }

theorem u689 : Upper (D 3) (R 3) [6,40,257,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b689
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b690 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 261 88 145 96 225 161 417), lower := (rows 7 42 261 88 145 96 64 128 256), losses := [] }

theorem u690 : Upper (D 3) (R 3) [6,40,257,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b690
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b691 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 261 88 145 160 97 225 353), lower := (rows 7 42 261 88 145 160 64 128 256), losses := [] }

theorem u691 : Upper (D 3) (R 3) [6,40,257,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b691
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r692 : Route 9 := (fun mask => (mask,id))

def c692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u692 : Upper (D 3) (R 3) [6,40,257,192,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192,96,1] 13 (by decide) (choices 1) [1,16,128] r692 c692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u91
  · exact u92
  · exact u93

def b693 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 261 200 112 48 193 129 385), lower := (rows 7 42 261 200 112 48 64 128 256), losses := [] }

theorem u693 : Upper (D 3) (R 3) [6,40,257,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b693
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 261 200 112 160 81 145 273), lower := (rows 7 42 261 200 112 160 64 128 256), losses := [] }

theorem u694 : Upper (D 3) (R 3) [6,40,257,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b694
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b695 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 276 73 145 33 224 224 480), lower := (rows 7 42 276 73 145 33 64 128 256), losses := [] }

theorem u695 : Upper (D 3) (R 3) [6,40,272,65,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b695
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b696 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 276 73 145 96 225 161 417), lower := (rows 7 42 276 73 145 96 64 128 256), losses := [] }

theorem u696 : Upper (D 3) (R 3) [6,40,272,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b696
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r697 : Route 9 := (fun mask => (mask,id))

def c697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u697 : Upper (D 3) (R 3) [6,40,272,65,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,129,128] 13 (by decide) (choices 1) [1,32] r697 c697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u94
  · exact u95

def b698 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 137 112 33 209 145 401), lower := (rows 7 42 324 137 112 33 64 128 256), losses := [] }

theorem u698 : Upper (D 3) (R 3) [6,40,320,129,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b698
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b699 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 324 137 112 48 193 129 385), lower := (rows 7 42 324 137 112 48 64 128 256), losses := [] }

theorem u699 : Upper (D 3) (R 3) [6,40,320,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b699
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b700 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 324 137 112 160 81 145 273), lower := (rows 7 42 324 137 112 160 64 128 256), losses := [] }

theorem u700 : Upper (D 3) (R 3) [6,40,320,129,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b700
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 137 176 33 81 209 337), lower := (rows 7 42 324 137 176 33 64 128 256), losses := [] }

theorem u701 : Upper (D 3) (R 3) [6,40,320,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b701
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b702 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 7 42 324 137 176 48 65 193 321), lower := (rows 7 42 324 137 176 48 64 128 256), losses := [] }

theorem u702 : Upper (D 3) (R 3) [6,40,320,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b702
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r703 : Route 9 := (fun mask => (mask,id))

def c703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u703 : Upper (D 3) (R 3) [6,40,320,129,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,160,64] 13 (by decide) (choices 1) [1,16] r703 c703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u96
  · exact u97

def b704 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 137 208 33 113 177 305), lower := (rows 7 42 324 137 208 33 64 128 256), losses := [] }

theorem u704 : Upper (D 3) (R 3) [6,40,320,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b704
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 324 137 208 48 97 161 289), lower := (rows 7 42 324 137 208 48 64 128 256), losses := [] }

theorem u705 : Upper (D 3) (R 3) [6,40,320,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b705
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 25 152 33 224 224 480), lower := (rows 7 98 261 25 152 33 64 128 256), losses := [] }

theorem u706 : Upper (D 3) (R 3) [6,96,257,17,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b706
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 261 25 152 96 225 161 417), lower := (rows 7 98 261 25 152 96 64 128 256), losses := [] }

theorem u707 : Upper (D 3) (R 3) [6,96,257,17,136,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b707
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 25 152 160 97 225 353), lower := (rows 7 98 261 25 152 160 64 128 256), losses := [] }

theorem u708 : Upper (D 3) (R 3) [6,96,257,17,136,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b708
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 261 56 145 33 200 200 456), lower := (rows 7 98 261 56 145 33 64 128 256), losses := [] }

theorem u709 : Upper (D 3) (R 3) [6,96,257,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b709
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 98 261 56 145 40 193 193 449), lower := (rows 7 98 261 56 145 40 64 128 256), losses := [] }

theorem u710 : Upper (D 3) (R 3) [6,96,257,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b710
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 261 56 145 96 201 137 393), lower := (rows 7 98 261 56 145 96 64 128 256), losses := [] }

theorem u711 : Upper (D 3) (R 3) [6,96,257,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b711
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 56 145 160 73 201 329), lower := (rows 7 98 261 56 145 160 64 128 256), losses := [] }

theorem u712 : Upper (D 3) (R 3) [6,96,257,48,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b712
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r713 : Route 9 := (fun mask => (mask,id))

def c713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u713 : Upper (D 3) (R 3) [6,96,257,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,192,1] 13 (by decide) (choices 1) [1,8,128] r713 c713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u98
  · exact u99
  · exact u100

def b714 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 261 56 208 40 193 129 385), lower := (rows 7 98 261 56 208 40 64 128 256), losses := [] }

theorem u714 : Upper (D 3) (R 3) [6,96,257,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b714
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b715 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 56 208 160 73 137 265), lower := (rows 7 98 261 56 208 160 64 128 256), losses := [] }

theorem u715 : Upper (D 3) (R 3) [6,96,257,48,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b715
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 261 137 176 33 88 216 344), lower := (rows 7 98 261 137 176 33 64 128 256), losses := [] }

theorem u716 : Upper (D 3) (R 3) [6,96,257,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b716
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b717 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 7 98 261 137 176 40 81 209 337), lower := (rows 7 98 261 137 176 40 64 128 256), losses := [] }

theorem u717 : Upper (D 3) (R 3) [6,96,257,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b717
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b718 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 7 98 261 137 176 48 73 201 329), lower := (rows 7 98 261 137 176 48 64 128 256), losses := [] }

theorem u718 : Upper (D 3) (R 3) [6,96,257,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b718
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b719 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 261 137 176 96 89 153 281), lower := (rows 7 98 261 137 176 96 64 128 256), losses := [] }

theorem u719 : Upper (D 3) (R 3) [6,96,257,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b719
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P03
