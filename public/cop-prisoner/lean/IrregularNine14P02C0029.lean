import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0027
import IrregularNine14P02C0028

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1740 : PairBound 9 := { available := 461, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 51 50 461 461 477 493 461 461 461), lower := (rows 51 50 4 8 16 32 64 128 256), losses := [] }

theorem u1740 : Upper (D 2) (R 2) [50,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1740
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1741 : Route 9 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1741 : Nat → Fin 9 := (fun mask => match mask with | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u1741 : Upper (D 2) (R 2) [50,65] 13 := by
  apply FastRouting.sound _ _ [50,65] 13 (by decide) (choices 2) [24,48,72,80,136,144,192,384] r1741 c1741
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1635
  · exact u1636
  · exact u1637
  · exact u1638
  · exact u1639
  · exact u1640
  · exact u1641
  · exact u1642

def r1742 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1742 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u1742 : Upper (D 2) (R 2) [50,68] 13 := by
  apply FastRouting.sound _ _ [50,68] 13 (by decide) (choices 2) [9,17,24,48,65,72,80,129,136,144,192,384] r1742 c1742
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1643
  · exact u1644
  · exact u1645
  · exact u1646
  · exact u1647
  · exact u1648
  · exact u1649
  · exact u1650
  · exact u1651
  · exact u1652
  · exact u1653
  · exact u1654

def b1743 : PairBound 9 := { available := 493, camps := [{ cop := 0, region := 460, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 51 82 493 493 509 493 493 493 493), lower := (rows 51 82 4 8 16 32 64 128 256), losses := [] }

theorem u1743 : Upper (D 2) (R 2) [50,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1743
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1744 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1744 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u1744 : Upper (D 2) (R 2) [50,192] 13 := by
  apply FastRouting.sound _ _ [50,192] 13 (by decide) (choices 2) [9,17,24,48,65,72,80,192,257,264,272,320] r1744 c1744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1655
  · exact u1656
  · exact u1657
  · exact u1658
  · exact u1659
  · exact u1660
  · exact u1661
  · exact u1662
  · exact u1663
  · exact u1664
  · exact u1665
  · exact u1666

def r1745 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1745 : Nat → Fin 9 := (fun _ => 0)

theorem u1745 : Upper (D 2) (R 2) [112,5] 13 := by
  apply FastRouting.sound _ _ [112,5] 13 (by decide) (choices 2) [10,18,24,48,130,136,144,384] r1745 c1745
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1667
  · exact u1668
  · exact u1669
  · exact u1670
  · exact u1671
  · exact u1672
  · exact u1673
  · exact u1674

theorem m1746_3 : Upper (D 2) (R 2) [112,12,3] 13 :=
  permutation_upper _ _ _ [112,5,10] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1667

def r1746 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1746 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u1746 : Upper (D 2) (R 2) [112,12] 13 := by
  apply FastRouting.sound _ _ [112,12] 13 (by decide) (choices 2) [3,17,18,48,129,130,144,384] r1746 c1746
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1746_3
  · exact u1679
  · exact u1680
  · exact u1681
  · exact u1682
  · exact u1683
  · exact u1684
  · exact u1685

def b1747 : PairBound 9 := { available := 494, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 494 494 510 494 494 494 494), lower := (rows 113 19 4 8 16 32 64 128 256), losses := [] }

theorem u1747 : Upper (D 2) (R 2) [112,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1747
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1748_3 : Upper (D 2) (R 2) [112,20,3] 13 :=
  permutation_upper _ _ _ [112,5,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1668

theorem m1748_9 : Upper (D 2) (R 2) [112,20,9] 13 :=
  permutation_upper _ _ _ [112,9,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1675

theorem m1748_10 : Upper (D 2) (R 2) [112,20,10] 13 :=
  permutation_upper _ _ _ [112,12,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1680

theorem m1748_33 : Upper (D 2) (R 2) [112,20,33] 13 :=
  permutation_upper _ _ _ [112,17,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1686

def r1748 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1748 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1748 : Upper (D 2) (R 2) [112,20] 13 := by
  apply FastRouting.sound _ _ [112,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,129,130,136,160,384] r1748 c1748
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1748_3
  · exact m1748_9
  · exact m1748_10
  · exact m1748_33
  · exact u1690
  · exact u1691
  · exact u1692
  · exact u1693
  · exact u1694
  · exact u1695
  · exact u1696
  · exact u1697

def b1749 : PairBound 9 := { available := 463, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 463 463 479 495 463 463 463), lower := (rows 113 50 4 8 16 32 64 128 256), losses := [] }

theorem u1749 : Upper (D 2) (R 2) [112,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1749
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1750_10 : Upper (D 2) (R 2) [112,129,10] 13 :=
  permutation_upper _ _ _ [112,12,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1682

theorem m1750_18 : Upper (D 2) (R 2) [112,129,18] 13 :=
  permutation_upper _ _ _ [112,20,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1693

theorem m1750_24 : Upper (D 2) (R 2) [112,129,24] 13 :=
  permutation_upper _ _ _ [112,24,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1698

theorem m1750_48 : Upper (D 2) (R 2) [112,129,48] 13 :=
  permutation_upper _ _ _ [112,48,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1702

def r1750 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c1750 : Nat → Fin 9 := (fun _ => 0)

theorem u1750 : Upper (D 2) (R 2) [112,129] 13 := by
  apply FastRouting.sound _ _ [112,129] 13 (by decide) (choices 2) [10,18,24,48,130,136,144,258,264,272,384] r1750 c1750
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1750_10
  · exact m1750_18
  · exact m1750_24
  · exact m1750_48
  · exact u1706
  · exact u1707
  · exact u1708
  · exact u1709
  · exact u1710
  · exact u1711
  · exact u1712

theorem m1751_3 : Upper (D 2) (R 2) [112,132,3] 13 :=
  permutation_upper _ _ _ [112,5,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1671

theorem m1751_9 : Upper (D 2) (R 2) [112,132,9] 13 :=
  permutation_upper _ _ _ [112,9,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1676

theorem m1751_10 : Upper (D 2) (R 2) [112,132,10] 13 :=
  permutation_upper _ _ _ [112,12,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1683

theorem m1751_17 : Upper (D 2) (R 2) [112,132,17] 13 :=
  permutation_upper _ _ _ [112,17,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1687

theorem m1751_18 : Upper (D 2) (R 2) [112,132,18] 13 :=
  permutation_upper _ _ _ [112,20,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1694

theorem m1751_24 : Upper (D 2) (R 2) [112,132,24] 13 :=
  permutation_upper _ _ _ [112,24,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1699

theorem m1751_48 : Upper (D 2) (R 2) [112,132,48] 13 :=
  permutation_upper _ _ _ [112,48,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1703

theorem m1751_129 : Upper (D 2) (R 2) [112,132,129] 13 :=
  permutation_upper _ _ _ [112,129,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1706

theorem m1751_257 : Upper (D 2) (R 2) [112,132,257] 13 :=
  permutation_upper _ _ _ [112,129,258] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1709

def r1751 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c1751 : Nat → Fin 9 := (fun _ => 0)

theorem u1751 : Upper (D 2) (R 2) [112,132] 13 := by
  apply FastRouting.sound _ _ [112,132] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,129,130,136,144,257,258,264,272,384] r1751 c1751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1751_3
  · exact m1751_9
  · exact m1751_10
  · exact m1751_17
  · exact m1751_18
  · exact m1751_24
  · exact m1751_48
  · exact m1751_129
  · exact u1713
  · exact u1714
  · exact u1715
  · exact m1751_257
  · exact u1716
  · exact u1717
  · exact u1718
  · exact u1719

theorem m1752_3 : Upper (D 2) (R 2) [112,144,3] 13 :=
  permutation_upper _ _ _ [112,5,144] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1673

theorem m1752_9 : Upper (D 2) (R 2) [112,144,9] 13 :=
  permutation_upper _ _ _ [112,9,144] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1677

theorem m1752_10 : Upper (D 2) (R 2) [112,144,10] 13 :=
  permutation_upper _ _ _ [112,12,144] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1684

theorem m1752_33 : Upper (D 2) (R 2) [112,144,33] 13 :=
  permutation_upper _ _ _ [112,17,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1688

theorem m1752_34 : Upper (D 2) (R 2) [112,144,34] 13 :=
  permutation_upper _ _ _ [112,20,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1696

theorem m1752_40 : Upper (D 2) (R 2) [112,144,40] 13 :=
  permutation_upper _ _ _ [112,24,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1700

theorem m1752_96 : Upper (D 2) (R 2) [112,144,96] 13 :=
  permutation_upper _ _ _ [112,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1704

theorem m1752_129 : Upper (D 2) (R 2) [112,144,129] 13 :=
  permutation_upper _ _ _ [112,129,144] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1708

theorem m1752_130 : Upper (D 2) (R 2) [112,144,130] 13 :=
  permutation_upper _ _ _ [112,132,144] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1715

theorem m1752_136 : Upper (D 2) (R 2) [112,144,136] 13 :=
  permutation_upper _ _ _ [112,136,144] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1720

theorem m1752_257 : Upper (D 2) (R 2) [112,144,257] 13 :=
  permutation_upper _ _ _ [112,129,272] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1711

theorem m1752_258 : Upper (D 2) (R 2) [112,144,258] 13 :=
  permutation_upper _ _ _ [112,132,272] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1718

theorem m1752_264 : Upper (D 2) (R 2) [112,144,264] 13 :=
  permutation_upper _ _ _ [112,136,272] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1721

def r1752 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1752 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1752 : Upper (D 2) (R 2) [112,144] 13 := by
  apply FastRouting.sound _ _ [112,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,129,130,136,160,257,258,264,288,384] r1752 c1752
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1752_3
  · exact m1752_9
  · exact m1752_10
  · exact m1752_33
  · exact m1752_34
  · exact m1752_40
  · exact m1752_96
  · exact m1752_129
  · exact m1752_130
  · exact m1752_136
  · exact u1723
  · exact m1752_257
  · exact m1752_258
  · exact m1752_264
  · exact u1724
  · exact u1725

theorem m1753_3 : Upper (D 2) (R 2) [112,384,3] 13 :=
  permutation_upper _ _ _ [112,5,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1674

theorem m1753_9 : Upper (D 2) (R 2) [112,384,9] 13 :=
  permutation_upper _ _ _ [112,9,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1678

theorem m1753_10 : Upper (D 2) (R 2) [112,384,10] 13 :=
  permutation_upper _ _ _ [112,12,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1685

theorem m1753_17 : Upper (D 2) (R 2) [112,384,17] 13 :=
  permutation_upper _ _ _ [112,17,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1689

theorem m1753_18 : Upper (D 2) (R 2) [112,384,18] 13 :=
  permutation_upper _ _ _ [112,20,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1697

theorem m1753_24 : Upper (D 2) (R 2) [112,384,24] 13 :=
  permutation_upper _ _ _ [112,24,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1701

theorem m1753_48 : Upper (D 2) (R 2) [112,384,48] 13 :=
  permutation_upper _ _ _ [112,48,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1705

theorem m1753_129 : Upper (D 2) (R 2) [112,384,129] 13 :=
  permutation_upper _ _ _ [112,129,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1712

theorem m1753_130 : Upper (D 2) (R 2) [112,384,130] 13 :=
  permutation_upper _ _ _ [112,132,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1719

theorem m1753_136 : Upper (D 2) (R 2) [112,384,136] 13 :=
  permutation_upper _ _ _ [112,136,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1722

theorem m1753_144 : Upper (D 2) (R 2) [112,384,144] 13 :=
  permutation_upper _ _ _ [112,144,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1725

def r1753 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1753 : Nat → Fin 9 := (fun _ => 0)

theorem u1753 : Upper (D 2) (R 2) [112,384] 13 := by
  apply FastRouting.sound _ _ [112,384] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,129,130,136,144,384] r1753 c1753
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1753_3
  · exact m1753_9
  · exact m1753_10
  · exact m1753_17
  · exact m1753_18
  · exact m1753_24
  · exact m1753_48
  · exact m1753_129
  · exact m1753_130
  · exact m1753_136
  · exact m1753_144
  · exact u1726

def r1754 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 257 => (17,(fun i => match i.val with | 4 => 8 | 8 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 272 => (48,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 288 => (48,(fun i => match i.val with | 4 => 8 | 8 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 320 => (48,(fun i => match i.val with | 4 => 6 | 5 => 8 | 6 => 4 | 8 => 5 | _ => i)) | 384 => (48,(fun i => match i.val with | 4 => 7 | 5 => 8 | 7 => 4 | 8 => 5 | _ => i)) | _ => (mask,id))

def c1754 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u1754 : Upper (D 2) (R 2) [14] 13 := by
  apply FastRouting.sound _ _ [14] 13 (by decide) (choices 2) [17,48] r1754 c1754
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1727
  · exact u1728

def r1755 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 257 => (33,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 264 => (40,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 272 => (48,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (96,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 384 => (96,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | _ => (mask,id))

def c1755 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1755 : Upper (D 2) (R 2) [22] 13 := by
  apply FastRouting.sound _ _ [22] 13 (by decide) (choices 2) [9,17,24,33,40,48,96] r1755 c1755
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1729
  · exact u1730
  · exact u1731
  · exact u1732
  · exact u1733
  · exact u1734
  · exact u1735

def r1756 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 264 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c1756 : Nat → Fin 9 := (fun _ => 0)

theorem u1756 : Upper (D 2) (R 2) [50] 13 := by
  apply FastRouting.sound _ _ [50] 13 (by decide) (choices 2) [5,12,17,20,48,65,68,80,192] r1756 c1756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1736
  · exact u1737
  · exact u1738
  · exact u1739
  · exact u1740
  · exact u1741
  · exact u1742
  · exact u1743
  · exact u1744

def r1757 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 136 => (132,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 264 => (132,(fun i => match i.val with | 2 => 3 | 3 => 2 | 7 => 8 | 8 => 7 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1757 : Nat → Fin 9 := (fun _ => 0)

theorem u1757 : Upper (D 2) (R 2) [112] 13 := by
  apply FastRouting.sound _ _ [112] 13 (by decide) (choices 2) [5,12,17,20,48,129,132,144,384] r1757 c1757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1745
  · exact u1746
  · exact u1747
  · exact u1748
  · exact u1749
  · exact u1750
  · exact u1751
  · exact u1752
  · exact u1753

def r1758 : Route 9 := (fun mask => match mask with | 38 => (22,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 70 => (22,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 134 => (22,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 262 => (22,(fun i => match i.val with | 4 => 8 | 8 => 4 | _ => i)) | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 42 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 74 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 138 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 7 | 7 => 4 | _ => i)) | 266 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 8 | 8 => 4 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 146 => (50,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 274 => (50,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 98 => (50,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 162 => (50,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 290 => (50,(fun i => match i.val with | 4 => 8 | 8 => 4 | _ => i)) | 194 => (50,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 322 => (50,(fun i => match i.val with | 4 => 6 | 5 => 8 | 6 => 4 | 8 => 5 | _ => i)) | 386 => (50,(fun i => match i.val with | 4 => 7 | 5 => 8 | 7 => 4 | 8 => 5 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 44 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 76 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 140 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 268 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 8 | 8 => 4 | _ => i)) | 52 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 84 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 148 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 276 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 8 | 8 => 5 | _ => i)) | 100 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 164 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 292 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 8 | 8 => 4 | _ => i)) | 196 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 324 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 6 | 5 => 8 | 6 => 4 | 8 => 5 | _ => i)) | 388 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 7 | 5 => 8 | 7 => 4 | 8 => 5 | _ => i)) | 56 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 88 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 152 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 280 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 8 | 8 => 5 | _ => i)) | 104 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 168 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 296 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 8 | 8 => 4 | _ => i)) | 200 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 328 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 6 | 5 => 8 | 6 => 4 | 8 => 5 | _ => i)) | 392 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 7 | 5 => 8 | 7 => 4 | 8 => 5 | _ => i)) | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 304 => (112,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 336 => (112,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 400 => (112,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | 224 => (112,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 352 => (112,(fun i => match i.val with | 4 => 8 | 8 => 4 | _ => i)) | 416 => (112,(fun i => match i.val with | 4 => 7 | 6 => 8 | 7 => 4 | 8 => 6 | _ => i)) | 448 => (112,(fun i => match i.val with | 4 => 7 | 5 => 8 | 7 => 4 | 8 => 5 | _ => i)) | _ => (mask,id))

def c1758 : Nat → Fin 9 := (fun _ => 0)

theorem u1758 : Upper (D 2) (R 2) [] 13 := by
  apply FastRouting.sound _ _ [] 13 (by decide) (choices 3) [14,22,50,112] r1758 c1758
    (by exact cover_three)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1754
  · exact u1755
  · exact u1756
  · exact u1757

#print axioms u1758
end Delivery.IrregularNine14.P02
