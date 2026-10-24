import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0003

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1680 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 13 168 80 48 194 130 386), lower := (rows 277 98 13 168 80 48 64 128 256), losses := [] }

theorem u1680 : Upper (D 1) (R 1) [276,96,9,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1680
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1681 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 277 98 13 168 80 160 82 146 274), lower := (rows 277 98 13 168 80 160 64 128 256), losses := [] }

theorem u1681 : Upper (D 1) (R 1) [276,96,9,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1681
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1682 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 14 137 48 34 208 208 464), lower := (rows 277 98 14 137 48 34 64 128 256), losses := [] }

theorem u1682 : Upper (D 1) (R 1) [276,96,10,129,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1682
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1683 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 14 137 48 48 194 194 450), lower := (rows 277 98 14 137 48 48 64 128 256), losses := [] }

theorem u1683 : Upper (D 1) (R 1) [276,96,10,129,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1683
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1684 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 14 137 48 96 210 146 402), lower := (rows 277 98 14 137 48 96 64 128 256), losses := [] }

theorem u1684 : Upper (D 1) (R 1) [276,96,10,129,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1684
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1685 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 14 137 48 160 82 210 338), lower := (rows 277 98 14 137 48 160 64 128 256), losses := [] }

theorem u1685 : Upper (D 1) (R 1) [276,96,10,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1685
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1686 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 44 73 144 34 210 146 402), lower := (rows 277 98 44 73 144 34 64 128 256), losses := [] }

theorem u1686 : Upper (D 1) (R 1) [276,96,40,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1686
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1687 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 44 73 144 48 194 130 386), lower := (rows 277 98 44 73 144 48 64 128 256), losses := [] }

theorem u1687 : Upper (D 1) (R 1) [276,96,40,65,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1687
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1688 : Route 9 := (fun mask => (mask,id))

def c1688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1688 : Upper (D 1) (R 1) [276,96,40,65,128,128] 13 := by
  apply FastRouting.sound _ _ [276,96,40,65,128,128] 13 (by decide) (choices 1) [2,16] r1688 c1688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u196
  · exact u197

def b1689 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 44 137 80 34 210 146 402), lower := (rows 277 98 44 137 80 34 64 128 256), losses := [] }

theorem u1689 : Upper (D 1) (R 1) [276,96,40,129,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1689
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1690 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 44 137 80 48 194 130 386), lower := (rows 277 98 44 137 80 48 64 128 256), losses := [] }

theorem u1690 : Upper (D 1) (R 1) [276,96,40,129,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1690
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1691 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 277 98 44 137 80 160 82 146 274), lower := (rows 277 98 44 137 80 160 64 128 256), losses := [] }

theorem u1691 : Upper (D 1) (R 1) [276,96,40,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1691
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1692 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 98 44 138 80 33 210 146 402), lower := (rows 277 98 44 138 80 33 64 128 256), losses := [] }

theorem u1692 : Upper (D 1) (R 1) [276,96,40,130,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1692
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1693 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 44 138 80 34 209 145 401), lower := (rows 277 98 44 138 80 34 64 128 256), losses := [] }

theorem u1693 : Upper (D 1) (R 1) [276,96,40,130,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1693
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1694 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 44 138 80 48 195 131 387), lower := (rows 277 98 44 138 80 48 64 128 256), losses := [] }

theorem u1694 : Upper (D 1) (R 1) [276,96,40,130,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1694
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1695 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 277 98 44 138 80 160 83 147 275), lower := (rows 277 98 44 138 80 160 64 128 256), losses := [] }

theorem u1695 : Upper (D 1) (R 1) [276,96,40,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1695
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1696 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 98 44 200 18 33 210 146 402), lower := (rows 277 98 44 200 18 33 64 128 256), losses := [] }

theorem u1696 : Upper (D 1) (R 1) [276,96,40,192,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1696
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1697 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 44 200 18 34 209 145 401), lower := (rows 277 98 44 200 18 34 64 128 256), losses := [] }

theorem u1697 : Upper (D 1) (R 1) [276,96,40,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1697
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1698 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 50, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 44 200 18 48 195 131 387), lower := (rows 277 98 44 200 18 48 64 128 256), losses := [] }

theorem u1698 : Upper (D 1) (R 1) [276,96,40,192,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1698
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1699 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 277 98 44 200 18 160 83 147 275), lower := (rows 277 98 44 200 18 160 64 128 256), losses := [] }

theorem u1699 : Upper (D 1) (R 1) [276,96,40,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1699
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1700 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 277 98 134 11 48 40 208 208 464), lower := (rows 277 98 134 11 48 40 64 128 256), losses := [] }

theorem u1700 : Upper (D 1) (R 1) [276,96,130,3,32,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1700
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1701 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 134 11 48 48 200 200 456), lower := (rows 277 98 134 11 48 48 64 128 256), losses := [] }

theorem u1701 : Upper (D 1) (R 1) [276,96,130,3,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1701
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1702 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 134 11 48 96 216 152 408), lower := (rows 277 98 134 11 48 96 64 128 256), losses := [] }

theorem u1702 : Upper (D 1) (R 1) [276,96,130,3,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1702
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1703 : PairBound 9 := { available := 88, camps := [], pairs := [(0,7)], upper := (rows 277 98 134 11 48 160 88 216 344), lower := (rows 277 98 134 11 48 160 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 12 50 32 77 0 269), good := (rows 349 114 351 347 48 48 64 0 256) }] }

theorem u1703 : Upper (D 1) (R 1) [276,96,130,3,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1703
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1704 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 134 41 80 34 216 152 408), lower := (rows 277 98 134 41 80 34 64 128 256), losses := [] }

theorem u1704 : Upper (D 1) (R 1) [276,96,130,33,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1704
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1705 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 98 134 41 80 40 210 146 402), lower := (rows 277 98 134 41 80 40 64 128 256), losses := [] }

theorem u1705 : Upper (D 1) (R 1) [276,96,130,33,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1705
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1706 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 134 41 80 48 202 138 394), lower := (rows 277 98 134 41 80 48 64 128 256), losses := [] }

theorem u1706 : Upper (D 1) (R 1) [276,96,130,33,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1706
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1707 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 134 41 80 160 90 154 282), lower := (rows 277 98 134 41 80 160 64 128 256), losses := [] }

theorem u1707 : Upper (D 1) (R 1) [276,96,130,33,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1707
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1708 : PairBound 9 := { available := 26, camps := [], pairs := [], upper := (rows 277 98 134 168 80 33 90 154 282), lower := (rows 277 98 134 168 80 33 64 128 256), losses := [] }

theorem u1708 : Upper (D 1) (R 1) [276,96,130,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1708
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1709 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 134 168 80 34 89 153 281), lower := (rows 277 98 134 168 80 34 64 128 256), losses := [] }

theorem u1709 : Upper (D 1) (R 1) [276,96,130,160,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1709
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1710 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 277 98 134 168 80 40 83 147 275), lower := (rows 277 98 134 168 80 40 64 128 256), losses := [] }

theorem u1710 : Upper (D 1) (R 1) [276,96,130,160,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1710
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1711 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 134 168 80 48 75 139 267), lower := (rows 277 98 134 168 80 48 64 128 256), losses := [] }

theorem u1711 : Upper (D 1) (R 1) [276,96,130,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1711
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1712 : PairBound 9 := { available := 208, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 140 11 48 34 208 208 464), lower := (rows 277 98 140 11 48 34 64 128 256), losses := [] }

theorem u1712 : Upper (D 1) (R 1) [276,96,136,3,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1712
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1713 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 140 11 48 48 194 194 450), lower := (rows 277 98 140 11 48 48 64 128 256), losses := [] }

theorem u1713 : Upper (D 1) (R 1) [276,96,136,3,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1713
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1714 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 140 11 48 96 210 146 402), lower := (rows 277 98 140 11 48 96 64 128 256), losses := [] }

theorem u1714 : Upper (D 1) (R 1) [276,96,136,3,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1714
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1715 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 140 11 48 160 82 210 338), lower := (rows 277 98 140 11 48 160 64 128 256), losses := [] }

theorem u1715 : Upper (D 1) (R 1) [276,96,136,3,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1715
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1716 : PairBound 9 := { available := 208, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 140 41 18 34 208 208 464), lower := (rows 277 98 140 41 18 34 64 128 256), losses := [] }

theorem u1716 : Upper (D 1) (R 1) [276,96,136,33,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1716
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1717 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 140 41 18 48 194 194 450), lower := (rows 277 98 140 41 18 48 64 128 256), losses := [] }

theorem u1717 : Upper (D 1) (R 1) [276,96,136,33,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1717
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1718 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 140 41 18 96 210 146 402), lower := (rows 277 98 140 41 18 96 64 128 256), losses := [] }

theorem u1718 : Upper (D 1) (R 1) [276,96,136,33,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1718
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1719 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 140 41 18 160 82 210 338), lower := (rows 277 98 140 41 18 160 64 128 256), losses := [] }

theorem u1719 : Upper (D 1) (R 1) [276,96,136,33,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1719
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1720 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 140 41 80 34 210 146 402), lower := (rows 277 98 140 41 80 34 64 128 256), losses := [] }

theorem u1720 : Upper (D 1) (R 1) [276,96,136,33,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1720
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1721 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 140 41 80 48 194 130 386), lower := (rows 277 98 140 41 80 48 64 128 256), losses := [] }

theorem u1721 : Upper (D 1) (R 1) [276,96,136,33,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1721
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1722 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 140 41 80 160 82 146 274), lower := (rows 277 98 140 41 80 160 64 128 256), losses := [] }

theorem u1722 : Upper (D 1) (R 1) [276,96,136,33,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1722
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1723 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 277 98 164 11 18 40 208 208 464), lower := (rows 277 98 164 11 18 40 64 128 256), losses := [] }

theorem u1723 : Upper (D 1) (R 1) [276,96,160,3,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1723
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1724 : PairBound 9 := { available := 200, camps := [{ cop := 6, region := 50, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 11 18 48 200 200 456), lower := (rows 277 98 164 11 18 48 64 128 256), losses := [] }

theorem u1724 : Upper (D 1) (R 1) [276,96,160,3,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1724
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1725 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 164 11 18 96 216 152 408), lower := (rows 277 98 164 11 18 96 64 128 256), losses := [] }

theorem u1725 : Upper (D 1) (R 1) [276,96,160,3,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1725
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1726 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 277 98 164 11 18 160 88 216 344), lower := (rows 277 98 164 11 18 160 64 128 256), losses := [] }

theorem u1726 : Upper (D 1) (R 1) [276,96,160,3,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1726
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1727 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 164 11 80 34 216 152 408), lower := (rows 277 98 164 11 80 34 64 128 256), losses := [] }

theorem u1727 : Upper (D 1) (R 1) [276,96,160,3,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1727
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1728 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 98 164 11 80 40 210 146 402), lower := (rows 277 98 164 11 80 40 64 128 256), losses := [] }

theorem u1728 : Upper (D 1) (R 1) [276,96,160,3,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1728
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1729 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 11 80 48 202 138 394), lower := (rows 277 98 164 11 80 48 64 128 256), losses := [] }

theorem u1729 : Upper (D 1) (R 1) [276,96,160,3,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1729
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1730 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 277 98 164 11 80 160 90 154 282), lower := (rows 277 98 164 11 80 160 64 128 256), losses := [] }

theorem u1730 : Upper (D 1) (R 1) [276,96,160,3,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1730
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1731 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 164 73 18 34 216 152 408), lower := (rows 277 98 164 73 18 34 64 128 256), losses := [] }

theorem u1731 : Upper (D 1) (R 1) [276,96,160,65,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1731
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1732 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 98 164 73 18 40 210 146 402), lower := (rows 277 98 164 73 18 40 64 128 256), losses := [] }

theorem u1732 : Upper (D 1) (R 1) [276,96,160,65,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1732
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1733 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 50, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 73 18 48 202 138 394), lower := (rows 277 98 164 73 18 48 64 128 256), losses := [] }

theorem u1733 : Upper (D 1) (R 1) [276,96,160,65,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1733
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1734 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 277 98 164 73 18 160 90 154 282), lower := (rows 277 98 164 73 18 160 64 128 256), losses := [] }

theorem u1734 : Upper (D 1) (R 1) [276,96,160,65,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1734
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1735 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 277 98 164 138 18 33 88 216 344), lower := (rows 277 98 164 138 18 33 64 128 256), losses := [] }

theorem u1735 : Upper (D 1) (R 1) [276,96,160,130,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1735
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1736 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 277 98 164 138 18 40 81 209 337), lower := (rows 277 98 164 138 18 40 64 128 256), losses := [] }

theorem u1736 : Upper (D 1) (R 1) [276,96,160,130,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1736
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1737 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 52, targets := 64 }], pairs := [(2,6)], upper := (rows 277 98 164 138 18 48 73 201 329), lower := (rows 277 98 164 138 18 48 64 128 256), losses := [] }

theorem u1737 : Upper (D 1) (R 1) [276,96,160,130,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1737
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1738 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 277 98 164 138 18 96 89 153 281), lower := (rows 277 98 164 138 18 96 64 128 256), losses := [] }

theorem u1738 : Upper (D 1) (R 1) [276,96,160,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1738
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1739 : PairBound 9 := { available := 26, camps := [], pairs := [], upper := (rows 277 98 164 138 80 33 90 154 282), lower := (rows 277 98 164 138 80 33 64 128 256), losses := [] }

theorem u1739 : Upper (D 1) (R 1) [276,96,160,130,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1739
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1739
end Delivery.IrregularNine14.P01
