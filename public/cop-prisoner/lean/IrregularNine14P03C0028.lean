import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0004

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1680 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 7 388 42 88 48 193 129 385), lower := (rows 97 7 388 42 88 48 64 128 256), losses := [] }

theorem u1680 : Upper (D 3) (R 3) [96,5,384,34,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1680
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1681 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 42 88 160 81 145 273), lower := (rows 97 7 388 42 88 160 64 128 256), losses := [] }

theorem u1681 : Upper (D 3) (R 3) [96,5,384,34,72,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1681
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1682 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 42 145 33 88 216 344), lower := (rows 97 7 388 42 145 33 64 128 256), losses := [] }

theorem u1682 : Upper (D 3) (R 3) [96,5,384,34,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1682
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1683 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 7 388 42 145 40 81 209 337), lower := (rows 97 7 388 42 145 40 64 128 256), losses := [] }

theorem u1683 : Upper (D 3) (R 3) [96,5,384,34,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1683
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1684 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 7 388 42 145 48 73 201 329), lower := (rows 97 7 388 42 145 48 64 128 256), losses := [] }

theorem u1684 : Upper (D 3) (R 3) [96,5,384,34,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1684
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1685 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 42 145 96 89 153 281), lower := (rows 97 7 388 42 145 96 64 128 256), losses := [] }

theorem u1685 : Upper (D 3) (R 3) [96,5,384,34,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1685
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1686 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 42 208 33 89 153 281), lower := (rows 97 7 388 42 208 33 64 128 256), losses := [] }

theorem u1686 : Upper (D 3) (R 3) [96,5,384,34,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1686
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1687 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 7 388 42 208 40 81 145 273), lower := (rows 97 7 388 42 208 40 64 128 256), losses := [] }

theorem u1687 : Upper (D 3) (R 3) [96,5,384,34,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1687
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1688 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 7 388 42 208 48 73 137 265), lower := (rows 97 7 388 42 208 48 64 128 256), losses := [] }

theorem u1688 : Upper (D 3) (R 3) [96,5,384,34,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1688
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1689 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 56 145 33 74 202 330), lower := (rows 97 7 388 56 145 33 64 128 256), losses := [] }

theorem u1689 : Upper (D 3) (R 3) [96,5,384,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1689
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1690 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 7 388 56 145 34 73 201 329), lower := (rows 97 7 388 56 145 34 64 128 256), losses := [] }

theorem u1690 : Upper (D 3) (R 3) [96,5,384,48,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1690
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1691 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 7 388 56 145 40 67 195 323), lower := (rows 97 7 388 56 145 40 64 128 256), losses := [] }

theorem u1691 : Upper (D 3) (R 3) [96,5,384,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1691
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1692 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 388 56 145 96 75 139 267), lower := (rows 97 7 388 56 145 96 64 128 256), losses := [] }

theorem u1692 : Upper (D 3) (R 3) [96,5,384,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1692
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1693 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 388 56 208 33 75 139 267), lower := (rows 97 7 388 56 208 33 64 128 256), losses := [] }

theorem u1693 : Upper (D 3) (R 3) [96,5,384,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1693
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1694 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 7 388 56 208 34 73 137 265), lower := (rows 97 7 388 56 208 34 64 128 256), losses := [] }

theorem u1694 : Upper (D 3) (R 3) [96,5,384,48,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1694
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1695 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 7 388 56 208 40 67 131 259), lower := (rows 97 7 388 56 208 40 64 128 256), losses := [] }

theorem u1695 : Upper (D 3) (R 3) [96,5,384,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1695
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1696 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 137 273 33 224 224 480), lower := (rows 97 14 22 137 273 33 64 128 256), losses := [] }

theorem u1696 : Upper (D 3) (R 3) [96,12,18,129,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1696
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1697 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 137 273 96 225 161 417), lower := (rows 97 14 22 137 273 96 64 128 256), losses := [] }

theorem u1697 : Upper (D 3) (R 3) [96,12,18,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1697
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1698 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 22 137 273 160 97 225 353), lower := (rows 97 14 22 137 273 160 64 128 256), losses := [] }

theorem u1698 : Upper (D 3) (R 3) [96,12,18,129,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1698
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1699 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 137 273 33 194 194 450), lower := (rows 97 14 52 137 273 33 64 128 256), losses := [] }

theorem u1699 : Upper (D 3) (R 3) [96,12,48,129,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1699
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1700 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 14 52 137 273 34 193 193 449), lower := (rows 97 14 52 137 273 34 64 128 256), losses := [] }

theorem u1700 : Upper (D 3) (R 3) [96,12,48,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1700
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1701 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 137 273 96 195 131 387), lower := (rows 97 14 52 137 273 96 64 128 256), losses := [] }

theorem u1701 : Upper (D 3) (R 3) [96,12,48,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1701
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1702 : Route 9 := (fun mask => (mask,id))

def c1702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1702 : Upper (D 3) (R 3) [96,12,48,129,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,257,128] 13 (by decide) (choices 1) [1,2] r1702 c1702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u277
  · exact u278

def b1703 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 336 33 195 131 387), lower := (rows 97 14 52 137 336 33 64 128 256), losses := [] }

theorem u1703 : Upper (D 3) (R 3) [96,12,48,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1703
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1704 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 52 137 336 34 193 129 385), lower := (rows 97 14 52 137 336 34 64 128 256), losses := [] }

theorem u1704 : Upper (D 3) (R 3) [96,12,48,129,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1704
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1705 : Route 9 := (fun mask => (mask,id))

def c1705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1705 : Upper (D 3) (R 3) [96,12,48,129,320,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,320,128] 13 (by decide) (choices 1) [1,2] r1705 c1705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u279
  · exact u280

def b1706 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 200 273 33 195 131 387), lower := (rows 97 14 52 200 273 33 64 128 256), losses := [] }

theorem u1706 : Upper (D 3) (R 3) [96,12,48,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1706
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1707 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 52 200 273 34 193 129 385), lower := (rows 97 14 52 200 273 34 64 128 256), losses := [] }

theorem u1707 : Upper (D 3) (R 3) [96,12,48,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1707
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1708 : Route 9 := (fun mask => (mask,id))

def c1708 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1708 : Upper (D 3) (R 3) [96,12,48,192,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,257,128] 13 (by decide) (choices 1) [1,2] r1708 c1708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u281
  · exact u282

def b1709 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 265 145 33 194 194 450), lower := (rows 97 14 52 265 145 33 64 128 256), losses := [] }

theorem u1709 : Upper (D 3) (R 3) [96,12,48,257,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1709
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1710 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 14 52 265 145 34 193 193 449), lower := (rows 97 14 52 265 145 34 64 128 256), losses := [] }

theorem u1710 : Upper (D 3) (R 3) [96,12,48,257,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1710
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1711 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 265 145 96 195 131 387), lower := (rows 97 14 52 265 145 96 64 128 256), losses := [] }

theorem u1711 : Upper (D 3) (R 3) [96,12,48,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1711
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1712 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 265 145 160 67 195 323), lower := (rows 97 14 52 265 145 160 64 128 256), losses := [] }

theorem u1712 : Upper (D 3) (R 3) [96,12,48,257,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1712
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1713 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 265 208 33 195 131 387), lower := (rows 97 14 52 265 208 33 64 128 256), losses := [] }

theorem u1713 : Upper (D 3) (R 3) [96,12,48,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1713
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1714 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 52 265 208 34 193 129 385), lower := (rows 97 14 52 265 208 34 64 128 256), losses := [] }

theorem u1714 : Upper (D 3) (R 3) [96,12,48,257,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1714
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1715 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 265 208 160 67 131 259), lower := (rows 97 14 52 265 208 160 64 128 256), losses := [] }

theorem u1715 : Upper (D 3) (R 3) [96,12,48,257,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1715
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1716 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 328 145 33 195 131 387), lower := (rows 97 14 52 328 145 33 64 128 256), losses := [] }

theorem u1716 : Upper (D 3) (R 3) [96,12,48,320,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1716
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1717 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 52 328 145 34 193 129 385), lower := (rows 97 14 52 328 145 34 64 128 256), losses := [] }

theorem u1717 : Upper (D 3) (R 3) [96,12,48,320,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1717
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1718 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 328 145 160 67 131 259), lower := (rows 97 14 52 328 145 160 64 128 256), losses := [] }

theorem u1718 : Upper (D 3) (R 3) [96,12,48,320,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1718
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1719 : PairBound 9 := { available := 208, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 265 50 33 208 208 464), lower := (rows 97 14 133 265 50 33 64 128 256), losses := [] }

theorem u1719 : Upper (D 3) (R 3) [96,12,129,257,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1719
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1720 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 14 133 265 50 48 193 193 449), lower := (rows 97 14 133 265 50 48 64 128 256), losses := [] }

theorem u1720 : Upper (D 3) (R 3) [96,12,129,257,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1720
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1721 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 133 265 50 96 209 145 401), lower := (rows 97 14 133 265 50 96 64 128 256), losses := [] }

theorem u1721 : Upper (D 3) (R 3) [96,12,129,257,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1721
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1722 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 265 50 160 81 209 337), lower := (rows 97 14 133 265 50 160 64 128 256), losses := [] }

theorem u1722 : Upper (D 3) (R 3) [96,12,129,257,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1722
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1723 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 133 265 176 33 82 210 338), lower := (rows 97 14 133 265 176 33 64 128 256), losses := [] }

theorem u1723 : Upper (D 3) (R 3) [96,12,129,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1723
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1724 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 14 133 265 176 34 81 209 337), lower := (rows 97 14 133 265 176 34 64 128 256), losses := [] }

theorem u1724 : Upper (D 3) (R 3) [96,12,129,257,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1724
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1725 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 14 133 265 176 48 67 195 323), lower := (rows 97 14 133 265 176 48 64 128 256), losses := [] }

theorem u1725 : Upper (D 3) (R 3) [96,12,129,257,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1725
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1726 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 133 265 176 96 83 147 275), lower := (rows 97 14 133 265 176 96 64 128 256), losses := [] }

theorem u1726 : Upper (D 3) (R 3) [96,12,129,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1726
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1727 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 296 82 33 209 145 401), lower := (rows 97 14 133 296 82 33 64 128 256), losses := [] }

theorem u1727 : Upper (D 3) (R 3) [96,12,129,288,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1727
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1728 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 133 296 82 48 193 129 385), lower := (rows 97 14 133 296 82 48 64 128 256), losses := [] }

theorem u1728 : Upper (D 3) (R 3) [96,12,129,288,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1728
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1729 : Route 9 := (fun mask => (mask,id))

def c1729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1729 : Upper (D 3) (R 3) [96,12,129,288,66,128] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,66,128] 13 (by decide) (choices 1) [1,16] r1729 c1729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u283
  · exact u284

def b1730 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 296 208 33 83 147 275), lower := (rows 97 14 133 296 208 33 64 128 256), losses := [] }

theorem u1730 : Upper (D 3) (R 3) [96,12,129,288,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1730
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1731 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 14 133 296 208 34 81 145 273), lower := (rows 97 14 133 296 208 34 64 128 256), losses := [] }

theorem u1731 : Upper (D 3) (R 3) [96,12,129,288,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1731
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1732 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 14 133 296 208 48 67 131 259), lower := (rows 97 14 133 296 208 48 64 128 256), losses := [] }

theorem u1732 : Upper (D 3) (R 3) [96,12,129,288,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1732
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1733 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 265 82 33 209 145 401), lower := (rows 97 14 164 265 82 33 64 128 256), losses := [] }

theorem u1733 : Upper (D 3) (R 3) [96,12,160,257,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1733
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1734 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 14 164 265 82 48 193 129 385), lower := (rows 97 14 164 265 82 48 64 128 256), losses := [] }

theorem u1734 : Upper (D 3) (R 3) [96,12,160,257,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1734
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1735 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 164 265 82 160 81 145 273), lower := (rows 97 14 164 265 82 160 64 128 256), losses := [] }

theorem u1735 : Upper (D 3) (R 3) [96,12,160,257,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1735
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1736 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 164 265 145 33 82 210 338), lower := (rows 97 14 164 265 145 33 64 128 256), losses := [] }

theorem u1736 : Upper (D 3) (R 3) [96,12,160,257,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1736
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1737 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 14 164 265 145 34 81 209 337), lower := (rows 97 14 164 265 145 34 64 128 256), losses := [] }

theorem u1737 : Upper (D 3) (R 3) [96,12,160,257,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1737
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1738 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 14 164 265 145 48 67 195 323), lower := (rows 97 14 164 265 145 48 64 128 256), losses := [] }

theorem u1738 : Upper (D 3) (R 3) [96,12,160,257,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1738
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1739 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 164 265 145 96 83 147 275), lower := (rows 97 14 164 265 145 96 64 128 256), losses := [] }

theorem u1739 : Upper (D 3) (R 3) [96,12,160,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1739
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1739
end Delivery.IrregularNine14.P03
