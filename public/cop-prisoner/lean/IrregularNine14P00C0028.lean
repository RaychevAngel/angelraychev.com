import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0009

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1680 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 14 148 296 18 225 193 193 449), lower := (rows 113 14 148 296 18 32 64 128 256), losses := [] }

theorem u1680 : Upper (D 0) (R 0) [112,12,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1680
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1681 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 148 296 80 163 195 131 387), lower := (rows 113 14 148 296 80 32 64 128 256), losses := [] }

theorem u1681 : Upper (D 0) (R 0) [112,12,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1681
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1682 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 296 144 99 67 195 323), lower := (rows 113 14 148 296 144 32 64 128 256), losses := [] }

theorem u1682 : Upper (D 0) (R 0) [112,12,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1682
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1683 : PairBound 9 := { available := 450, camps := [], pairs := [(1,5)], upper := (rows 113 22 44 137 17 482 450 450 450), lower := (rows 113 22 44 137 17 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 25 0 70 134 262), good := (rows 81 470 478 153 17 0 64 128 256) }] }

theorem u1683 : Upper (D 0) (R 0) [112,20,40,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1683
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1684 : PairBound 9 := { available := 449, camps := [], pairs := [], upper := (rows 113 22 44 137 18 481 449 449 449), lower := (rows 113 22 44 137 18 32 64 128 256), losses := [] }

theorem u1684 : Upper (D 0) (R 0) [112,20,40,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1684
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1685 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 137 80 419 451 387 387), lower := (rows 113 22 44 137 80 32 64 128 256), losses := [] }

theorem u1685 : Upper (D 0) (R 0) [112,20,40,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1685
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1686 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 44 137 144 355 323 451 323), lower := (rows 113 22 44 137 144 32 64 128 256), losses := [] }

theorem u1686 : Upper (D 0) (R 0) [112,20,40,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1686
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1687 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 44 137 272 227 195 195 451), lower := (rows 113 22 44 137 272 32 64 128 256), losses := [] }

theorem u1687 : Upper (D 0) (R 0) [112,20,40,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1687
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1688 : PairBound 9 := { available := 449, camps := [], pairs := [(2,4)], upper := (rows 113 22 44 138 17 481 449 449 449), lower := (rows 113 22 44 138 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 6 10 0 49 81 145 273), good := (rows 481 494 44 142 481 32 64 128 256) }] }

theorem u1688 : Upper (D 0) (R 0) [112,20,40,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1688
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1689 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 138 80 417 449 385 385), lower := (rows 113 22 44 138 80 32 64 128 256), losses := [] }

theorem u1689 : Upper (D 0) (R 0) [112,20,40,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1689
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1690 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 44 138 144 353 321 449 321), lower := (rows 113 22 44 138 144 32 64 128 256), losses := [] }

theorem u1690 : Upper (D 0) (R 0) [112,20,40,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1690
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1691 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 44 138 272 225 193 193 449), lower := (rows 113 22 44 138 272 32 64 128 256), losses := [] }

theorem u1691 : Upper (D 0) (R 0) [112,20,40,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1691
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1692 : Route 9 := (fun mask => (mask,id))

def c1692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1692 : Upper (D 0) (R 0) [112,20,40,192,1] 13 := by
  apply FastRouting.sound _ _ [112,20,40,192,1] 13 (by decide) (choices 1) [1,2,128,256] r1692 c1692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u555
  · exact u556
  · exact u557
  · exact u558

def b1693 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 113 22 44 200 18 417 449 385 385), lower := (rows 113 22 44 200 18 32 64 128 256), losses := [] }

theorem u1693 : Upper (D 0) (R 0) [112,20,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1693
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1694 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 44 200 144 291 323 387 259), lower := (rows 113 22 44 200 144 32 64 128 256), losses := [] }

theorem u1694 : Upper (D 0) (R 0) [112,20,40,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1694
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1695 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 44 200 272 163 195 131 387), lower := (rows 113 22 44 200 272 32 64 128 256), losses := [] }

theorem u1695 : Upper (D 0) (R 0) [112,20,40,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1695
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1696 : PairBound 9 := { available := 194, camps := [], pairs := [(1,5)], upper := (rows 113 22 44 265 17 226 194 194 450), lower := (rows 113 22 44 265 17 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 25 0 70 134 262), good := (rows 81 470 478 281 17 0 64 128 256) }] }

theorem u1696 : Upper (D 0) (R 0) [112,20,40,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1696
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1697 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 44 265 18 225 193 193 449), lower := (rows 113 22 44 265 18 32 64 128 256), losses := [] }

theorem u1697 : Upper (D 0) (R 0) [112,20,40,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1697
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1698 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 265 80 163 195 131 387), lower := (rows 113 22 44 265 80 32 64 128 256), losses := [] }

theorem u1698 : Upper (D 0) (R 0) [112,20,40,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1698
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1699 : Route 9 := (fun mask => (mask,id))

def c1699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1699 : Upper (D 0) (R 0) [112,20,40,257,128] 13 := by
  apply FastRouting.sound _ _ [112,20,40,257,128] 13 (by decide) (choices 1) [1,2,64,128] r1699 c1699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u559
  · exact u560
  · exact u561
  · exact u562

def b1700 : PairBound 9 := { available := 193, camps := [], pairs := [(2,4)], upper := (rows 113 22 44 266 17 225 193 193 449), lower := (rows 113 22 44 266 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 6 10 0 49 81 145 273), good := (rows 481 494 44 270 481 32 64 128 256) }] }

theorem u1700 : Upper (D 0) (R 0) [112,20,40,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1700
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1701 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 266 80 161 193 129 385), lower := (rows 113 22 44 266 80 32 64 128 256), losses := [] }

theorem u1701 : Upper (D 0) (R 0) [112,20,40,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1701
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1702 : Route 9 := (fun mask => (mask,id))

def c1702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1702 : Upper (D 0) (R 0) [112,20,40,258,128] 13 := by
  apply FastRouting.sound _ _ [112,20,40,258,128] 13 (by decide) (choices 1) [1,64,128] r1702 c1702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u563
  · exact u564
  · exact u565

def r1703 : Route 9 := (fun mask => (mask,id))

def c1703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1703 : Upper (D 0) (R 0) [112,20,40,320,1] 13 := by
  apply FastRouting.sound _ _ [112,20,40,320,1] 13 (by decide) (choices 1) [1,2,128] r1703 c1703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u566
  · exact u567
  · exact u568

def b1704 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 113 22 44 328 18 161 193 129 385), lower := (rows 113 22 44 328 18 32 64 128 256), losses := [] }

theorem u1704 : Upper (D 0) (R 0) [112,20,40,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1704
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1705 : Route 9 := (fun mask => (mask,id))

def c1705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1705 : Upper (D 0) (R 0) [112,20,40,320,128] 13 := by
  apply FastRouting.sound _ _ [112,20,40,320,128] 13 (by decide) (choices 1) [1,2,128] r1705 c1705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u569
  · exact u570
  · exact u571

def r1706 : Route 9 := (fun mask => (mask,id))

def c1706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1706 : Upper (D 0) (R 0) [112,20,40,384,1] 13 := by
  apply FastRouting.sound _ _ [112,20,40,384,1] 13 (by decide) (choices 1) [1,2,64,128] r1706 c1706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u572
  · exact u573
  · exact u574
  · exact u575

def b1707 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 44 392 18 225 193 193 449), lower := (rows 113 22 44 392 18 32 64 128 256), losses := [] }

theorem u1707 : Upper (D 0) (R 0) [112,20,40,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1707
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1708 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 392 80 163 195 131 387), lower := (rows 113 22 44 392 80 32 64 128 256), losses := [] }

theorem u1708 : Upper (D 0) (R 0) [112,20,40,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1708
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1709 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 44 392 144 99 67 195 323), lower := (rows 113 22 44 392 144 32 64 128 256), losses := [] }

theorem u1709 : Upper (D 0) (R 0) [112,20,40,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1709
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1710 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 168 17 362 330 458 330), lower := (rows 113 22 133 168 17 32 64 128 256), losses := [] }

theorem u1710 : Upper (D 0) (R 0) [112,20,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1710
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1711 : PairBound 9 := { available := 329, camps := [], pairs := [], upper := (rows 113 22 133 168 18 361 329 457 329), lower := (rows 113 22 133 168 18 32 64 128 256), losses := [] }

theorem u1711 : Upper (D 0) (R 0) [112,20,129,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1711
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1712 : PairBound 9 := { available := 323, camps := [], pairs := [], upper := (rows 113 22 133 168 24 355 323 451 323), lower := (rows 113 22 133 168 24 32 64 128 256), losses := [] }

theorem u1712 : Upper (D 0) (R 0) [112,20,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1712
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1713 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 133 168 80 299 331 395 267), lower := (rows 113 22 133 168 80 32 64 128 256), losses := [] }

theorem u1713 : Upper (D 0) (R 0) [112,20,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1713
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1714 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 22 133 168 272 107 75 203 331), lower := (rows 113 22 133 168 272 32 64 128 256), losses := [] }

theorem u1714 : Upper (D 0) (R 0) [112,20,129,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1714
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1715 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 113 22 133 265 18 232 232 232 488), lower := (rows 113 22 133 265 18 32 64 128 256), losses := [] }

theorem u1715 : Upper (D 0) (R 0) [112,20,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1715
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1716 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 22 133 265 24 226 226 226 482), lower := (rows 113 22 133 265 24 32 64 128 256), losses := [] }

theorem u1716 : Upper (D 0) (R 0) [112,20,129,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1716
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1717 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 265 48 234 202 202 458), lower := (rows 113 22 133 265 48 32 64 128 256), losses := [] }

theorem u1717 : Upper (D 0) (R 0) [112,20,129,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1717
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1718 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 133 265 144 106 106 234 362), lower := (rows 113 22 133 265 144 32 64 128 256), losses := [] }

theorem u1718 : Upper (D 0) (R 0) [112,20,129,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1718
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1719 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 266 17 232 232 232 488), lower := (rows 113 22 133 266 17 32 64 128 256), losses := [] }

theorem u1719 : Upper (D 0) (R 0) [112,20,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1719
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1720 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 22 133 266 24 225 225 225 481), lower := (rows 113 22 133 266 24 32 64 128 256), losses := [] }

theorem u1720 : Upper (D 0) (R 0) [112,20,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1720
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1721 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 266 48 233 201 201 457), lower := (rows 113 22 133 266 48 32 64 128 256), losses := [] }

theorem u1721 : Upper (D 0) (R 0) [112,20,129,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1721
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1722 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 133 266 144 105 105 233 361), lower := (rows 113 22 133 266 144 32 64 128 256), losses := [] }

theorem u1722 : Upper (D 0) (R 0) [112,20,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1722
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1723 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 296 17 234 202 202 458), lower := (rows 113 22 133 296 17 32 64 128 256), losses := [] }

theorem u1723 : Upper (D 0) (R 0) [112,20,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1723
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1724 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 113 22 133 296 18 233 201 201 457), lower := (rows 113 22 133 296 18 32 64 128 256), losses := [] }

theorem u1724 : Upper (D 0) (R 0) [112,20,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1724
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1725 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 133 296 24 227 195 195 451), lower := (rows 113 22 133 296 24 32 64 128 256), losses := [] }

theorem u1725 : Upper (D 0) (R 0) [112,20,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1725
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1726 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 133 296 80 171 203 139 395), lower := (rows 113 22 133 296 80 32 64 128 256), losses := [] }

theorem u1726 : Upper (D 0) (R 0) [112,20,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1726
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1727 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 133 296 144 107 75 203 331), lower := (rows 113 22 133 296 144 32 64 128 256), losses := [] }

theorem u1727 : Upper (D 0) (R 0) [112,20,129,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1727
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1728 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 392 17 106 106 234 362), lower := (rows 113 22 133 392 17 32 64 128 256), losses := [] }

theorem u1728 : Upper (D 0) (R 0) [112,20,129,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1728
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1729 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 113 22 133 392 18 105 105 233 361), lower := (rows 113 22 133 392 18 32 64 128 256), losses := [] }

theorem u1729 : Upper (D 0) (R 0) [112,20,129,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1729
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1730 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 22 133 392 24 99 99 227 355), lower := (rows 113 22 133 392 24 32 64 128 256), losses := [] }

theorem u1730 : Upper (D 0) (R 0) [112,20,129,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1730
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1731 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 392 48 107 75 203 331), lower := (rows 113 22 133 392 48 32 64 128 256), losses := [] }

theorem u1731 : Upper (D 0) (R 0) [112,20,129,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1731
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1732 : PairBound 9 := { available := 226, camps := [], pairs := [(1,5)], upper := (rows 113 22 140 265 17 226 226 226 482), lower := (rows 113 22 140 265 17 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 25 0 64 128 256), good := (rows 81 22 158 281 17 0 64 128 256) }] }

theorem u1732 : Upper (D 0) (R 0) [112,20,136,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1732
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1733 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 22 140 265 18 225 225 225 481), lower := (rows 113 22 140 265 18 32 64 128 256), losses := [] }

theorem u1733 : Upper (D 0) (R 0) [112,20,136,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1733
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1734 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 265 48 227 195 195 451), lower := (rows 113 22 140 265 48 32 64 128 256), losses := [] }

theorem u1734 : Upper (D 0) (R 0) [112,20,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1734
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1735 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 140 265 144 99 99 227 355), lower := (rows 113 22 140 265 144 32 64 128 256), losses := [] }

theorem u1735 : Upper (D 0) (R 0) [112,20,136,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1735
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1736 : PairBound 9 := { available := 225, camps := [], pairs := [(2,4)], upper := (rows 113 22 140 266 17 225 225 225 481), lower := (rows 113 22 140 266 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 6 10 0 49 81 145 273), good := (rows 481 494 140 270 481 32 64 128 256) }] }

theorem u1736 : Upper (D 0) (R 0) [112,20,136,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1736
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1737 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 266 48 225 193 193 449), lower := (rows 113 22 140 266 48 32 64 128 256), losses := [] }

theorem u1737 : Upper (D 0) (R 0) [112,20,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1737
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1738 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 140 266 144 97 97 225 353), lower := (rows 113 22 140 266 144 32 64 128 256), losses := [] }

theorem u1738 : Upper (D 0) (R 0) [112,20,136,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1738
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1739 : Route 9 := (fun mask => (mask,id))

def c1739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1739 : Upper (D 0) (R 0) [112,20,136,288,1] 13 := by
  apply FastRouting.sound _ _ [112,20,136,288,1] 13 (by decide) (choices 1) [1,2,64,128] r1739 c1739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u576
  · exact u577
  · exact u578
  · exact u579

#print axioms u1739
end Delivery.IrregularNine14.P00
