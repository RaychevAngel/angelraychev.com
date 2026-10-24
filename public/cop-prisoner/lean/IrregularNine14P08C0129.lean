import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0022

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7740 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 292 152 208 41 105 169 297), lower := (rows 7 67 292 152 208 32 64 128 256), losses := [] }

theorem u7740 : Upper (D 8) (R 8) [6,65,288,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7741 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 292 168 176 121 89 217 345), lower := (rows 7 67 292 168 176 32 64 128 256), losses := [] }

theorem u7741 : Upper (D 8) (R 8) [6,65,288,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7742 : Route 9 := (fun mask => (mask,id))

def c7742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7742 : Upper (D 8) (R 8) [6,65,288,160,192] 13 := by
  apply FastRouting.sound _ _ [6,65,288,160,192] 13 (by decide) (choices 1) [1,8,16] r7742 c7742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1354
  · exact u1355
  · exact u1356

def b7743 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 25 56 224 224 224 480), lower := (rows 7 67 388 25 56 32 64 128 256), losses := [] }

theorem u7743 : Upper (D 8) (R 8) [6,65,384,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7744 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 388 25 88 160 224 160 416), lower := (rows 7 67 388 25 88 32 64 128 256), losses := [] }

theorem u7744 : Upper (D 8) (R 8) [6,65,384,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7745 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 25 112 168 232 168 424), lower := (rows 7 67 388 25 112 32 64 128 256), losses := [] }

theorem u7745 : Upper (D 8) (R 8) [6,65,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7746 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 388 25 152 96 96 224 352), lower := (rows 7 67 388 25 152 32 64 128 256), losses := [] }

theorem u7746 : Upper (D 8) (R 8) [6,65,384,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7747 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 25 176 104 104 232 360), lower := (rows 7 67 388 25 176 32 64 128 256), losses := [] }

theorem u7747 : Upper (D 8) (R 8) [6,65,384,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7748 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 25 208 40 104 168 296), lower := (rows 7 67 388 25 208 32 64 128 256), losses := [] }

theorem u7748 : Upper (D 8) (R 8) [6,65,384,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7749 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 41 56 240 240 240 496), lower := (rows 7 67 388 41 56 32 64 128 256), losses := [] }

theorem u7749 : Upper (D 8) (R 8) [6,65,384,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7750 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 41 88 176 240 176 432), lower := (rows 7 67 388 41 88 32 64 128 256), losses := [] }

theorem u7750 : Upper (D 8) (R 8) [6,65,384,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7751 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 41 112 184 248 184 440), lower := (rows 7 67 388 41 112 32 64 128 256), losses := [] }

theorem u7751 : Upper (D 8) (R 8) [6,65,384,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7752 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 41 152 112 112 240 368), lower := (rows 7 67 388 41 152 32 64 128 256), losses := [] }

theorem u7752 : Upper (D 8) (R 8) [6,65,384,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7753 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 41 176 120 120 248 376), lower := (rows 7 67 388 41 176 32 64 128 256), losses := [] }

theorem u7753 : Upper (D 8) (R 8) [6,65,384,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7754 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 41 208 56 120 184 312), lower := (rows 7 67 388 41 208 32 64 128 256), losses := [] }

theorem u7754 : Upper (D 8) (R 8) [6,65,384,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7755 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 388 56 56 225 225 225 481), lower := (rows 7 67 388 56 56 32 64 128 256), losses := [] }

theorem u7755 : Upper (D 8) (R 8) [6,65,384,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7756 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 67 388 56 81 168 232 168 424), lower := (rows 7 67 388 56 81 32 64 128 256), losses := [] }

theorem u7756 : Upper (D 8) (R 8) [6,65,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7757 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 67 388 56 88 161 225 161 417), lower := (rows 7 67 388 56 88 32 64 128 256), losses := [] }

theorem u7757 : Upper (D 8) (R 8) [6,65,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7758 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 388 56 112 169 233 169 425), lower := (rows 7 67 388 56 112 32 64 128 256), losses := [] }

theorem u7758 : Upper (D 8) (R 8) [6,65,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7759 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 56 145 104 104 232 360), lower := (rows 7 67 388 56 145 32 64 128 256), losses := [] }

theorem u7759 : Upper (D 8) (R 8) [6,65,384,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7760 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 388 56 152 97 97 225 353), lower := (rows 7 67 388 56 152 32 64 128 256), losses := [] }

theorem u7760 : Upper (D 8) (R 8) [6,65,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7761 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 388 56 176 105 105 233 361), lower := (rows 7 67 388 56 176 32 64 128 256), losses := [] }

theorem u7761 : Upper (D 8) (R 8) [6,65,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7762 : Route 9 := (fun mask => (mask,id))

def c7762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7762 : Upper (D 8) (R 8) [6,65,384,48,192] 13 := by
  apply FastRouting.sound _ _ [6,65,384,48,192] 13 (by decide) (choices 1) [1,8] r7762 c7762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1357
  · exact u1358

def b7763 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 388 73 152 48 112 176 304), lower := (rows 7 67 388 73 152 32 64 128 256), losses := [] }

theorem u7763 : Upper (D 8) (R 8) [6,65,384,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7764 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 388 73 176 56 120 184 312), lower := (rows 7 67 388 73 176 32 64 128 256), losses := [] }

theorem u7764 : Upper (D 8) (R 8) [6,65,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7765 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 88 145 40 104 168 296), lower := (rows 7 67 388 88 145 32 64 128 256), losses := [] }

theorem u7765 : Upper (D 8) (R 8) [6,65,384,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7766 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 67 388 88 152 33 97 161 289), lower := (rows 7 67 388 88 152 32 64 128 256), losses := [] }

theorem u7766 : Upper (D 8) (R 8) [6,65,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7766 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7767 : Route 9 := (fun mask => (mask,id))

def c7767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7767 : Upper (D 8) (R 8) [6,65,384,80,160] 13 := by
  apply FastRouting.sound _ _ [6,65,384,80,160] 13 (by decide) (choices 1) [1,8] r7767 c7767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1359
  · exact u1360

def b7768 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 104 145 56 120 184 312), lower := (rows 7 67 388 104 145 32 64 128 256), losses := [] }

theorem u7768 : Upper (D 8) (R 8) [6,65,384,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7769 : Route 9 := (fun mask => (mask,id))

def c7769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7769 : Upper (D 8) (R 8) [6,65,384,96,136] 13 := by
  apply FastRouting.sound _ _ [6,65,384,96,136] 13 (by decide) (choices 1) [1,16] r7769 c7769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1361
  · exact u1362

def r7770 : Route 9 := (fun mask => (mask,id))

def c7770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7770 : Upper (D 8) (R 8) [6,65,384,96,160] 13 := by
  apply FastRouting.sound _ _ [6,65,384,96,160] 13 (by decide) (choices 1) [1,8,16] r7770 c7770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1363
  · exact u1364
  · exact u1365

def b7771 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 148 41 49 480 480 480 480), lower := (rows 7 74 148 41 49 32 64 128 256), losses := [] }

theorem u7771 : Upper (D 8) (R 8) [6,72,144,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7772 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 148 41 81 416 480 416 416), lower := (rows 7 74 148 41 81 32 64 128 256), losses := [] }

theorem u7772 : Upper (D 8) (R 8) [6,72,144,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7773 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 148 41 112 417 481 417 417), lower := (rows 7 74 148 41 112 32 64 128 256), losses := [] }

theorem u7773 : Upper (D 8) (R 8) [6,72,144,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7774 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 148 41 145 352 352 480 352), lower := (rows 7 74 148 41 145 32 64 128 256), losses := [] }

theorem u7774 : Upper (D 8) (R 8) [6,72,144,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7775 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 148 41 176 353 353 481 353), lower := (rows 7 74 148 41 176 32 64 128 256), losses := [] }

theorem u7775 : Upper (D 8) (R 8) [6,72,144,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7776 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 148 41 208 289 353 417 289), lower := (rows 7 74 148 41 208 32 64 128 256), losses := [] }

theorem u7776 : Upper (D 8) (R 8) [6,72,144,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7777 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 148 41 273 224 224 224 480), lower := (rows 7 74 148 41 273 32 64 128 256), losses := [] }

theorem u7777 : Upper (D 8) (R 8) [6,72,144,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7778 : Route 9 := (fun mask => (mask,id))

def c7778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7778 : Upper (D 8) (R 8) [6,72,144,33,288] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33,288] 13 (by decide) (choices 1) [1,64,128] r7778 c7778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1366
  · exact u1367
  · exact u1368

def b7779 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 148 41 336 161 225 161 417), lower := (rows 7 74 148 41 336 32 64 128 256), losses := [] }

theorem u7779 : Upper (D 8) (R 8) [6,72,144,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7780 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 107, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 148 41 400 97 97 225 353), lower := (rows 7 74 148 41 400 32 64 128 256), losses := [] }

theorem u7780 : Upper (D 8) (R 8) [6,72,144,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7781 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 73 273 160 224 160 416), lower := (rows 7 74 148 73 273 32 64 128 256), losses := [] }

theorem u7781 : Upper (D 8) (R 8) [6,72,144,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7782 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 73 304 161 225 161 417), lower := (rows 7 74 148 73 304 32 64 128 256), losses := [] }

theorem u7782 : Upper (D 8) (R 8) [6,72,144,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7783 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 104 273 161 225 161 417), lower := (rows 7 74 148 104 273 32 64 128 256), losses := [] }

theorem u7783 : Upper (D 8) (R 8) [6,72,144,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7784 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 104 304 161 225 161 417), lower := (rows 7 74 148 104 304 32 64 128 256), losses := [] }

theorem u7784 : Upper (D 8) (R 8) [6,72,144,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7785 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 148 137 273 96 96 224 352), lower := (rows 7 74 148 137 273 32 64 128 256), losses := [] }

theorem u7785 : Upper (D 8) (R 8) [6,72,144,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7786 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 148 137 304 97 97 225 353), lower := (rows 7 74 148 137 304 32 64 128 256), losses := [] }

theorem u7786 : Upper (D 8) (R 8) [6,72,144,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7787 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 148 168 273 97 97 225 353), lower := (rows 7 74 148 168 273 32 64 128 256), losses := [] }

theorem u7787 : Upper (D 8) (R 8) [6,72,144,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7788 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 148 168 304 97 97 225 353), lower := (rows 7 74 148 168 304 32 64 128 256), losses := [] }

theorem u7788 : Upper (D 8) (R 8) [6,72,144,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7789 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 200 273 33 97 161 289), lower := (rows 7 74 148 200 273 32 64 128 256), losses := [] }

theorem u7789 : Upper (D 8) (R 8) [6,72,144,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7790 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 200 304 33 97 161 289), lower := (rows 7 74 148 200 304 32 64 128 256), losses := [] }

theorem u7790 : Upper (D 8) (R 8) [6,72,144,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7791 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 74 164 25 49 480 480 480 480), lower := (rows 7 74 164 25 49 32 64 128 256), losses := [] }

theorem u7791 : Upper (D 8) (R 8) [6,72,160,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7792 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 7 74 164 25 81 416 480 416 416), lower := (rows 7 74 164 25 81 32 64 128 256), losses := [] }

theorem u7792 : Upper (D 8) (R 8) [6,72,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7793 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 25 112 417 481 417 417), lower := (rows 7 74 164 25 112 32 64 128 256), losses := [] }

theorem u7793 : Upper (D 8) (R 8) [6,72,160,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7794 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 25 145 352 352 480 352), lower := (rows 7 74 164 25 145 32 64 128 256), losses := [] }

theorem u7794 : Upper (D 8) (R 8) [6,72,160,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7795 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 164 25 176 353 353 481 353), lower := (rows 7 74 164 25 176 32 64 128 256), losses := [] }

theorem u7795 : Upper (D 8) (R 8) [6,72,160,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7796 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 25 208 289 353 417 289), lower := (rows 7 74 164 25 208 32 64 128 256), losses := [] }

theorem u7796 : Upper (D 8) (R 8) [6,72,160,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7797 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 74 164 25 273 224 224 224 480), lower := (rows 7 74 164 25 273 32 64 128 256), losses := [] }

theorem u7797 : Upper (D 8) (R 8) [6,72,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7798 : Route 9 := (fun mask => (mask,id))

def c7798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7798 : Upper (D 8) (R 8) [6,72,160,17,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,288] 13 (by decide) (choices 1) [1,64,128] r7798 c7798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1369
  · exact u1370
  · exact u1371

def b7799 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 25 336 161 225 161 417), lower := (rows 7 74 164 25 336 32 64 128 256), losses := [] }

theorem u7799 : Upper (D 8) (R 8) [6,72,160,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7799
end Delivery.IrregularNine14.P08
