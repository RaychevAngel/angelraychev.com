import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0010
import IrregularNine14P10C0011

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1740 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 168 400 313 345 409 281), lower := (rows 7 98 100 168 400 32 64 128 256), losses := [] }

theorem u1740 : Upper (D 10) (R 10) [6,96,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1740 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1741 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 464, targets := 32 },{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6),(4,5)], upper := (rows 7 98 164 41 88 432 464 400 400), lower := (rows 7 98 164 41 88 32 64 128 256), losses := [] }

theorem u1741 : Upper (D 10) (R 10) [6,96,160,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1741 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1742 : Route 9 := (fun mask => (mask,id))

def c1742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1742 : Upper (D 10) (R 10) [6,96,160,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,160,33,192] 13 (by decide) (choices 1) [8,16,256] r1742 c1742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u626
  · exact u627
  · exact u628

theorem m1743_128 : Upper (D 10) (R 10) [6,96,160,33,264,128] 13 :=
  permutation_upper _ _ _ [6,96,160,33,264,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u630

def r1743 : Route 9 := (fun mask => (mask,id))

def c1743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1743 : Upper (D 10) (R 10) [6,96,160,33,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,33,264] 13 (by decide) (choices 1) [16,64,128,256] r1743 c1743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u629
  · exact u630
  · exact m1743_128
  · exact u631

def r1744 : Route 9 := (fun mask => (mask,id))

def c1744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1744 : Upper (D 10) (R 10) [6,96,160,33,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,33,320] 13 (by decide) (choices 1) [8,16,128,256] r1744 c1744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u632
  · exact u633
  · exact u634
  · exact u635

def b1745 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 98 164 56 81 424 456 392 392), lower := (rows 7 98 164 56 81 32 64 128 256), losses := [] }

theorem u1745 : Upper (D 10) (R 10) [6,96,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1745 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1746 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 164 56 88 417 449 385 385), lower := (rows 7 98 164 56 88 32 64 128 256), losses := [] }

theorem u1746 : Upper (D 10) (R 10) [6,96,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1746 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1747 : Route 9 := (fun mask => (mask,id))

def c1747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1747 : Upper (D 10) (R 10) [6,96,160,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,192] 13 (by decide) (choices 1) [1,8,256] r1747 c1747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u636
  · exact u637
  · exact u638

theorem m1748_128 : Upper (D 10) (R 10) [6,96,160,48,257,128] 13 :=
  permutation_upper _ _ _ [6,96,160,48,257,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u640

def r1748 : Route 9 := (fun mask => (mask,id))

def c1748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u1748 : Upper (D 10) (R 10) [6,96,160,48,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,257] 13 (by decide) (choices 1) [8,64,128,256] r1748 c1748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u639
  · exact u640
  · exact m1748_128
  · exact u641

theorem m1749_128 : Upper (D 10) (R 10) [6,96,160,48,264,128] 13 :=
  permutation_upper _ _ _ [6,96,160,48,264,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u643

def r1749 : Route 9 := (fun mask => (mask,id))

def c1749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1749 : Upper (D 10) (R 10) [6,96,160,48,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,264] 13 (by decide) (choices 1) [1,64,128,256] r1749 c1749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u642
  · exact u643
  · exact m1749_128
  · exact u644

def r1750 : Route 9 := (fun mask => (mask,id))

def c1750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1750 : Upper (D 10) (R 10) [6,96,160,48,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,320] 13 (by decide) (choices 1) [1,8,128,256] r1750 c1750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u645
  · exact u646
  · exact u647
  · exact u648

def b1751 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 98 164 73 152 304 368 432 304), lower := (rows 7 98 164 73 152 32 64 128 256), losses := [] }

theorem u1751 : Upper (D 10) (R 10) [6,96,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1751 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1752 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 98 164 73 280 432 496 432 432), lower := (rows 7 98 164 73 280 32 64 128 256), losses := [] }

theorem u1752 : Upper (D 10) (R 10) [6,96,160,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1752 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1753 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 98 164 73 304 440 472 408 408), lower := (rows 7 98 164 73 304 32 64 128 256), losses := [] }

theorem u1753 : Upper (D 10) (R 10) [6,96,160,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1753 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1754 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 98 164 73 400 312 376 440 312), lower := (rows 7 98 164 73 400 32 64 128 256), losses := [] }

theorem u1754 : Upper (D 10) (R 10) [6,96,160,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1754 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1755 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 88 152 289 353 417 289), lower := (rows 7 98 164 88 152 32 64 128 256), losses := [] }

theorem u1755 : Upper (D 10) (R 10) [6,96,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1755 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1756 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 320 }], pairs := [(4,6),(4,8)], upper := (rows 7 98 164 88 176 297 329 393 265), lower := (rows 7 98 164 88 176 32 64 128 256), losses := [] }

theorem u1756 : Upper (D 10) (R 10) [6,96,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1756 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1757 : Route 9 := (fun mask => (mask,id))

def c1757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1757 : Upper (D 10) (R 10) [6,96,160,80,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,257] 13 (by decide) (choices 1) [8,128,256] r1757 c1757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u649
  · exact u650
  · exact u651

def b1758 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 88 280 417 481 417 417), lower := (rows 7 98 164 88 280 32 64 128 256), losses := [] }

theorem u1758 : Upper (D 10) (R 10) [6,96,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1758 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1759 : Route 9 := (fun mask => (mask,id))

def c1759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1759 : Upper (D 10) (R 10) [6,96,160,80,288] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,288] 13 (by decide) (choices 1) [1,8,128,256] r1759 c1759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u652
  · exact u653
  · exact u654
  · exact u655

def r1760 : Route 9 := (fun mask => (mask,id))

def c1760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1760 : Upper (D 10) (R 10) [6,96,160,80,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,384] 13 (by decide) (choices 1) [1,8,256] r1760 c1760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u656
  · exact u657
  · exact u658

def b1761 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 164 104 273 440 472 408 408), lower := (rows 7 98 164 104 273 32 64 128 256), losses := [] }

theorem u1761 : Upper (D 10) (R 10) [6,96,160,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1761 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1762 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 164 104 280 433 465 401 401), lower := (rows 7 98 164 104 280 32 64 128 256), losses := [] }

theorem u1762 : Upper (D 10) (R 10) [6,96,160,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1762 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1763 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 164 104 400 313 345 409 281), lower := (rows 7 98 164 104 400 32 64 128 256), losses := [] }

theorem u1763 : Upper (D 10) (R 10) [6,96,160,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1763 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1764 : Route 9 := (fun mask => (mask,id))

def c1764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1764 : Upper (D 10) (R 10) [6,96,160,192,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257] 13 (by decide) (choices 1) [8,16,256] r1764 c1764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u659
  · exact u660
  · exact u661

def r1765 : Route 9 := (fun mask => (mask,id))

def c1765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1765 : Upper (D 10) (R 10) [6,96,160,192,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,264] 13 (by decide) (choices 1) [1,16,256] r1765 c1765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u662
  · exact u663
  · exact u664

def r1766 : Route 9 := (fun mask => (mask,id))

def c1766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1766 : Upper (D 10) (R 10) [6,96,160,192,288] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,288] 13 (by decide) (choices 1) [1,8,16,256] r1766 c1766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u665
  · exact u666
  · exact u667
  · exact u668

def b1767 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 98 164 265 280 240 240 240 496), lower := (rows 7 98 164 265 280 32 64 128 256), losses := [] }

theorem u1767 : Upper (D 10) (R 10) [6,96,160,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1767 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m1768_128 : Upper (D 10) (R 10) [6,96,160,257,288,128] 13 :=
  permutation_upper _ _ _ [6,96,160,257,288,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u671

def r1768 : Route 9 := (fun mask => (mask,id))

def c1768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u1768 : Upper (D 10) (R 10) [6,96,160,257,288] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257,288] 13 (by decide) (choices 1) [8,16,64,128] r1768 c1768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u669
  · exact u670
  · exact u671
  · exact m1768_128

def r1769 : Route 9 := (fun mask => (mask,id))

def c1769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1769 : Upper (D 10) (R 10) [6,96,160,257,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257,320] 13 (by decide) (choices 1) [8,16,128] r1769 c1769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u672
  · exact u673
  · exact u674

def b1770 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 98 164 280 280 225 225 225 481), lower := (rows 7 98 164 280 280 32 64 128 256), losses := [] }

theorem u1770 : Upper (D 10) (R 10) [6,96,160,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1770 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1771 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 98 164 280 304 233 201 201 457), lower := (rows 7 98 164 280 304 32 64 128 256), losses := [] }

theorem u1771 : Upper (D 10) (R 10) [6,96,160,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1771 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1772 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 98 164 280 336 169 233 169 425), lower := (rows 7 98 164 280 336 32 64 128 256), losses := [] }

theorem u1772 : Upper (D 10) (R 10) [6,96,160,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1772 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1773 : Route 9 := (fun mask => (mask,id))

def c1773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1773 : Upper (D 10) (R 10) [6,96,160,288,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,288,320] 13 (by decide) (choices 1) [1,8,16,128] r1773 c1773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u675
  · exact u676
  · exact u677
  · exact u678

theorem m1774_16 : Upper (D 10) (R 10) [6,96,160,320,384,16] 13 :=
  permutation_upper _ _ _ [6,96,160,320,384,8] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u680

def r1774 : Route 9 := (fun mask => (mask,id))

def c1774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1774 : Upper (D 10) (R 10) [6,96,160,320,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,320,384] 13 (by decide) (choices 1) [1,8,16] r1774 c1774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u679
  · exact u680
  · exact m1774_16

def b1775 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 41 152 304 368 432 304), lower := (rows 7 98 196 41 152 32 64 128 256), losses := [] }

theorem u1775 : Upper (D 10) (R 10) [6,96,192,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1775 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1776 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 41 176 312 344 408 280), lower := (rows 7 98 196 41 176 32 64 128 256), losses := [] }

theorem u1776 : Upper (D 10) (R 10) [6,96,192,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1776 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1777 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 41 280 432 496 432 432), lower := (rows 7 98 196 41 280 32 64 128 256), losses := [] }

theorem u1777 : Upper (D 10) (R 10) [6,96,192,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1777 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1778 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 41 304 440 472 408 408), lower := (rows 7 98 196 41 304 32 64 128 256), losses := [] }

theorem u1778 : Upper (D 10) (R 10) [6,96,192,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1778 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1779 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 41 400 312 376 440 312), lower := (rows 7 98 196 41 400 32 64 128 256), losses := [] }

theorem u1779 : Upper (D 10) (R 10) [6,96,192,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1779 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1780 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 56 145 296 360 424 296), lower := (rows 7 98 196 56 145 32 64 128 256), losses := [] }

theorem u1780 : Upper (D 10) (R 10) [6,96,192,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1780 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1781 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 56 152 289 353 417 289), lower := (rows 7 98 196 56 152 32 64 128 256), losses := [] }

theorem u1781 : Upper (D 10) (R 10) [6,96,192,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1781 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1782 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 56 273 424 488 424 424), lower := (rows 7 98 196 56 273 32 64 128 256), losses := [] }

theorem u1782 : Upper (D 10) (R 10) [6,96,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1782 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1783 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 56 280 417 481 417 417), lower := (rows 7 98 196 56 280 32 64 128 256), losses := [] }

theorem u1783 : Upper (D 10) (R 10) [6,96,192,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1783 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1784 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 56 400 297 361 425 297), lower := (rows 7 98 196 56 400 32 64 128 256), losses := [] }

theorem u1784 : Upper (D 10) (R 10) [6,96,192,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1784 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1785 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 137 280 304 368 432 304), lower := (rows 7 98 196 137 280 32 64 128 256), losses := [] }

theorem u1785 : Upper (D 10) (R 10) [6,96,192,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1785 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1786 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 137 304 312 376 440 312), lower := (rows 7 98 196 137 304 32 64 128 256), losses := [] }

theorem u1786 : Upper (D 10) (R 10) [6,96,192,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1786 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1787 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 152 273 296 360 424 296), lower := (rows 7 98 196 152 273 32 64 128 256), losses := [] }

theorem u1787 : Upper (D 10) (R 10) [6,96,192,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1787 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1788 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 152 280 289 353 417 289), lower := (rows 7 98 196 152 280 32 64 128 256), losses := [] }

theorem u1788 : Upper (D 10) (R 10) [6,96,192,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1788 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1789 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 152 304 297 361 425 297), lower := (rows 7 98 196 152 304 32 64 128 256), losses := [] }

theorem u1789 : Upper (D 10) (R 10) [6,96,192,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1789 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1790 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 168 273 312 376 440 312), lower := (rows 7 98 196 168 273 32 64 128 256), losses := [] }

theorem u1790 : Upper (D 10) (R 10) [6,96,192,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1790 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1791 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 168 280 305 369 433 305), lower := (rows 7 98 196 168 280 32 64 128 256), losses := [] }

theorem u1791 : Upper (D 10) (R 10) [6,96,192,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1791 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1792 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 168 304 313 345 409 281), lower := (rows 7 98 196 168 304 32 64 128 256), losses := [] }

theorem u1792 : Upper (D 10) (R 10) [6,96,192,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1792 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1793 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 265 304 184 248 184 440), lower := (rows 7 98 196 265 304 32 64 128 256), losses := [] }

theorem u1793 : Upper (D 10) (R 10) [6,96,192,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1793 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1794 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 265 400 56 120 184 312), lower := (rows 7 98 196 265 400 32 64 128 256), losses := [] }

theorem u1794 : Upper (D 10) (R 10) [6,96,192,257,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1794 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1795 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 98 196 296 400 57 121 185 313), lower := (rows 7 98 196 296 400 32 64 128 256), losses := [] }

theorem u1795 : Upper (D 10) (R 10) [6,96,192,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1795 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1796 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 7 98 388 41 56 496 464 464 464), lower := (rows 7 98 388 41 56 32 64 128 256), losses := [] }

theorem u1796 : Upper (D 10) (R 10) [6,96,384,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1796 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1797 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1797 : Upper (D 10) (R 10) [6,96,384,33,72] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,72] 13 (by decide) (choices 1) [16,128] r1797 c1797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u681
  · exact u682

def b1798 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 16, targets := 384 }], pairs := [(4,7),(4,8)], upper := (rows 7 98 388 41 112 440 472 408 408), lower := (rows 7 98 388 41 112 32 64 128 256), losses := [] }

theorem u1798 : Upper (D 10) (R 10) [6,96,384,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1798 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1799 : Route 9 := (fun mask => (mask,id))

def c1799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1799 : Upper (D 10) (R 10) [6,96,384,33,136] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,136] 13 (by decide) (choices 1) [16,64,256] r1799 c1799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u683
  · exact u684
  · exact u685

#print axioms u1799
end Delivery.IrregularNine14.P10
