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

def r720 : Route 9 := (fun mask => (mask,id))

def c720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u720 : Upper (D 3) (R 3) [6,96,257,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,257,160,192,1] 13 (by decide) (choices 1) [1,8,16] r720 c720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u101
  · exact u102
  · exact u103

def b721 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 98 261 168 208 40 81 145 273), lower := (rows 7 98 261 168 208 40 64 128 256), losses := [] }

theorem u721 : Upper (D 3) (R 3) [6,96,257,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b721
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b722 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 98 261 168 208 48 73 137 265), lower := (rows 7 98 261 168 208 48 64 128 256), losses := [] }

theorem u722 : Upper (D 3) (R 3) [6,96,257,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b722
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b723 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 268 137 176 33 81 209 337), lower := (rows 7 98 268 137 176 33 64 128 256), losses := [] }

theorem u723 : Upper (D 3) (R 3) [6,96,264,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b723
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b724 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 7 98 268 137 176 48 65 193 321), lower := (rows 7 98 268 137 176 48 64 128 256), losses := [] }

theorem u724 : Upper (D 3) (R 3) [6,96,264,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b724
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b725 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 268 137 176 96 81 145 273), lower := (rows 7 98 268 137 176 96 64 128 256), losses := [] }

theorem u725 : Upper (D 3) (R 3) [6,96,264,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b725
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r726 : Route 9 := (fun mask => (mask,id))

def c726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u726 : Upper (D 3) (R 3) [6,96,384,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192,1] 13 (by decide) (choices 1) [1,8] r726 c726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u104
  · exact u105

def b727 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 7 98 388 56 208 40 65 129 257), lower := (rows 7 98 388 56 208 40 64 128 256), losses := [] }

theorem u727 : Upper (D 3) (R 3) [6,96,384,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b727
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 28 73 145 96 480 416 416), lower := (rows 35 7 28 73 145 96 64 128 256), losses := [] }

theorem u728 : Upper (D 3) (R 3) [34,5,24,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b728
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 7 28 73 145 288 224 224 480), lower := (rows 35 7 28 73 145 288 64 128 256), losses := [] }

theorem u729 : Upper (D 3) (R 3) [34,5,24,65,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b729
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 28 73 273 96 224 160 416), lower := (rows 35 7 28 73 273 96 64 128 256), losses := [] }

theorem u730 : Upper (D 3) (R 3) [34,5,24,65,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b730
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r731 : Route 9 := (fun mask => (mask,id))

def c731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u731 : Upper (D 3) (R 3) [34,5,24,65,257,128] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65,257,128] 13 (by decide) (choices 1) [32,128] r731 c731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u106
  · exact u107

def b732 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 73 400 33 224 224 480), lower := (rows 35 7 28 73 400 33 64 128 256), losses := [] }

theorem u732 : Upper (D 3) (R 3) [34,5,24,65,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b732
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 28 73 400 96 225 161 417), lower := (rows 35 7 28 73 400 96 64 128 256), losses := [] }

theorem u733 : Upper (D 3) (R 3) [34,5,24,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b733
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b734 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 28 73 400 160 97 225 353), lower := (rows 35 7 28 73 400 160 64 128 256), losses := [] }

theorem u734 : Upper (D 3) (R 3) [34,5,24,65,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b734
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b735 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 200 273 33 224 224 480), lower := (rows 35 7 28 200 273 33 64 128 256), losses := [] }

theorem u735 : Upper (D 3) (R 3) [34,5,24,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b735
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b736 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 28 200 273 96 225 161 417), lower := (rows 35 7 28 200 273 96 64 128 256), losses := [] }

theorem u736 : Upper (D 3) (R 3) [34,5,24,192,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b736
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b737 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 25 400 33 224 224 480), lower := (rows 35 7 76 25 400 33 64 128 256), losses := [] }

theorem u737 : Upper (D 3) (R 3) [34,5,72,17,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b737
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b738 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 25 400 96 225 161 417), lower := (rows 35 7 76 25 400 96 64 128 256), losses := [] }

theorem u738 : Upper (D 3) (R 3) [34,5,72,17,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b738
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b739 : PairBound 9 := { available := 97, camps := [], pairs := [(1,7)], upper := (rows 35 7 76 25 400 160 97 225 353), lower := (rows 35 7 76 25 400 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 32 65 0 257), good := (rows 355 327 78 351 272 32 64 0 256) }] }

theorem u739 : Upper (D 3) (R 3) [34,5,72,17,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b739
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 137 112 33 464 400 400), lower := (rows 35 7 76 137 112 33 64 128 256), losses := [] }

theorem u740 : Upper (D 3) (R 3) [34,5,72,129,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b740
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b741 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 35 7 76 137 112 48 449 385 385), lower := (rows 35 7 76 137 112 48 64 128 256), losses := [] }

theorem u741 : Upper (D 3) (R 3) [34,5,72,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b741
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b742 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 76 137 112 160 337 401 273), lower := (rows 35 7 76 137 112 160 64 128 256), losses := [] }

theorem u742 : Upper (D 3) (R 3) [34,5,72,129,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b742
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b743 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 7 76 137 112 288 209 145 401), lower := (rows 35 7 76 137 112 288 64 128 256), losses := [] }

theorem u743 : Upper (D 3) (R 3) [34,5,72,129,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b743
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b744 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 137 176 33 336 464 336), lower := (rows 35 7 76 137 176 33 64 128 256), losses := [] }

theorem u744 : Upper (D 3) (R 3) [34,5,72,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b744
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b745 : PairBound 9 := { available := 321, camps := [], pairs := [], upper := (rows 35 7 76 137 176 48 321 449 321), lower := (rows 35 7 76 137 176 48 64 128 256), losses := [] }

theorem u745 : Upper (D 3) (R 3) [34,5,72,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b745
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b746 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 137 176 96 337 401 273), lower := (rows 35 7 76 137 176 96 64 128 256), losses := [] }

theorem u746 : Upper (D 3) (R 3) [34,5,72,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b746
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b747 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 7 76 137 176 288 81 209 337), lower := (rows 35 7 76 137 176 288 64 128 256), losses := [] }

theorem u747 : Upper (D 3) (R 3) [34,5,72,129,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b747
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 137 208 33 368 432 304), lower := (rows 35 7 76 137 208 33 64 128 256), losses := [] }

theorem u748 : Upper (D 3) (R 3) [34,5,72,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b748
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 7 76 137 208 48 353 417 289), lower := (rows 35 7 76 137 208 48 64 128 256), losses := [] }

theorem u749 : Upper (D 3) (R 3) [34,5,72,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b749
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b750 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 7 76 137 208 288 113 177 305), lower := (rows 35 7 76 137 208 288 64 128 256), losses := [] }

theorem u750 : Upper (D 3) (R 3) [34,5,72,129,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b750
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b751 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 7 76 137 273 48 224 224 480), lower := (rows 35 7 76 137 273 48 64 128 256), losses := [] }

theorem u751 : Upper (D 3) (R 3) [34,5,72,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b751
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b752 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 137 273 96 240 176 432), lower := (rows 35 7 76 137 273 96 64 128 256), losses := [] }

theorem u752 : Upper (D 3) (R 3) [34,5,72,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b752
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 76 137 273 160 112 240 368), lower := (rows 35 7 76 137 273 160 64 128 256), losses := [] }

theorem u753 : Upper (D 3) (R 3) [34,5,72,129,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b753
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 137 304 33 208 208 464), lower := (rows 35 7 76 137 304 33 64 128 256), losses := [] }

theorem u754 : Upper (D 3) (R 3) [34,5,72,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b754
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b755 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 7 76 137 304 48 193 193 449), lower := (rows 35 7 76 137 304 48 64 128 256), losses := [] }

theorem u755 : Upper (D 3) (R 3) [34,5,72,129,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b755
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 137 304 96 209 145 401), lower := (rows 35 7 76 137 304 96 64 128 256), losses := [] }

theorem u756 : Upper (D 3) (R 3) [34,5,72,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b756
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 76 137 304 160 81 209 337), lower := (rows 35 7 76 137 304 160 64 128 256), losses := [] }

theorem u757 : Upper (D 3) (R 3) [34,5,72,129,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b757
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b758 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 137 336 33 240 176 432), lower := (rows 35 7 76 137 336 33 64 128 256), losses := [] }

theorem u758 : Upper (D 3) (R 3) [34,5,72,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b758
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b759 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 76 137 336 48 225 161 417), lower := (rows 35 7 76 137 336 48 64 128 256), losses := [] }

theorem u759 : Upper (D 3) (R 3) [34,5,72,129,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b759
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b760 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 76 137 336 160 113 177 305), lower := (rows 35 7 76 137 336 160 64 128 256), losses := [] }

theorem u760 : Upper (D 3) (R 3) [34,5,72,129,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b760
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b761 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 137 400 33 112 240 368), lower := (rows 35 7 76 137 400 33 64 128 256), losses := [] }

theorem u761 : Upper (D 3) (R 3) [34,5,72,129,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b761
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 7 76 137 400 48 97 225 353), lower := (rows 35 7 76 137 400 48 64 128 256), losses := [] }

theorem u762 : Upper (D 3) (R 3) [34,5,72,129,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b762
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b763 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 137 400 96 113 177 305), lower := (rows 35 7 76 137 400 96 64 128 256), losses := [] }

theorem u763 : Upper (D 3) (R 3) [34,5,72,129,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b763
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b764 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 152 273 33 224 224 480), lower := (rows 35 7 76 152 273 33 64 128 256), losses := [] }

theorem u764 : Upper (D 3) (R 3) [34,5,72,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b764
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 152 273 96 225 161 417), lower := (rows 35 7 76 152 273 96 64 128 256), losses := [] }

theorem u765 : Upper (D 3) (R 3) [34,5,72,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b765
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b766 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 76 152 273 160 97 225 353), lower := (rows 35 7 76 152 273 160 64 128 256), losses := [] }

theorem u766 : Upper (D 3) (R 3) [34,5,72,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b766
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b767 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 152 304 33 193 193 449), lower := (rows 35 7 76 152 304 33 64 128 256), losses := [] }

theorem u767 : Upper (D 3) (R 3) [34,5,72,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b767
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 152 304 96 193 129 385), lower := (rows 35 7 76 152 304 96 64 128 256), losses := [] }

theorem u768 : Upper (D 3) (R 3) [34,5,72,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b768
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b769 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 76 152 304 160 65 193 321), lower := (rows 35 7 76 152 304 160 64 128 256), losses := [] }

theorem u769 : Upper (D 3) (R 3) [34,5,72,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b769
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b770 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 265 112 33 208 144 400), lower := (rows 35 7 76 265 112 33 64 128 256), losses := [] }

theorem u770 : Upper (D 3) (R 3) [34,5,72,257,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b770
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 76 265 112 48 193 129 385), lower := (rows 35 7 76 265 112 48 64 128 256), losses := [] }

theorem u771 : Upper (D 3) (R 3) [34,5,72,257,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b771
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r772 : Route 9 := (fun mask => (mask,id))

def c772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u772 : Upper (D 3) (R 3) [34,5,72,257,96,128] 13 := by
  apply FastRouting.sound _ _ [34,5,72,257,96,128] 13 (by decide) (choices 1) [1,16,128] r772 c772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u108
  · exact u109
  · exact u110

def b773 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 7 76 265 145 48 224 224 480), lower := (rows 35 7 76 265 145 48 64 128 256), losses := [] }

theorem u773 : Upper (D 3) (R 3) [34,5,72,257,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b773
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b774 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 265 145 96 240 176 432), lower := (rows 35 7 76 265 145 96 64 128 256), losses := [] }

theorem u774 : Upper (D 3) (R 3) [34,5,72,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b774
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r775 : Route 9 := (fun mask => (mask,id))

def c775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u775 : Upper (D 3) (R 3) [34,5,72,257,129,128] 13 := by
  apply FastRouting.sound _ _ [34,5,72,257,129,128] 13 (by decide) (choices 1) [16,32] r775 c775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u111
  · exact u112

def b776 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 265 176 33 208 208 464), lower := (rows 35 7 76 265 176 33 64 128 256), losses := [] }

theorem u776 : Upper (D 3) (R 3) [34,5,72,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b776
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 7 76 265 176 48 193 193 449), lower := (rows 35 7 76 265 176 48 64 128 256), losses := [] }

theorem u777 : Upper (D 3) (R 3) [34,5,72,257,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b777
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b778 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 265 176 96 209 145 401), lower := (rows 35 7 76 265 176 96 64 128 256), losses := [] }

theorem u778 : Upper (D 3) (R 3) [34,5,72,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b778
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 265 176 160 81 209 337), lower := (rows 35 7 76 265 176 160 64 128 256), losses := [] }

theorem u779 : Upper (D 3) (R 3) [34,5,72,257,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b779
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P03
