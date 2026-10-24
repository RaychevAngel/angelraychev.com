import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0004

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1740 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 21 104 400 33 224 224 480), lower := (rows 35 14 21 104 400 33 64 128 256), losses := [] }

theorem u1740 : Upper (D 8) (R 8) [34,12,17,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1741 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 104 400 96 225 161 417), lower := (rows 35 14 21 104 400 96 64 128 256), losses := [] }

theorem u1741 : Upper (D 8) (R 8) [34,12,17,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1742 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 35 14 21 104 400 160 97 225 353), lower := (rows 35 14 21 104 400 160 64 128 256), losses := [] }

theorem u1742 : Upper (D 8) (R 8) [34,12,17,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1743 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 21 200 304 33 224 224 480), lower := (rows 35 14 21 200 304 33 64 128 256), losses := [] }

theorem u1743 : Upper (D 8) (R 8) [34,12,17,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1744 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 21 200 304 96 225 161 417), lower := (rows 35 14 21 200 304 96 64 128 256), losses := [] }

theorem u1744 : Upper (D 8) (R 8) [34,12,17,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1745 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 21 296 112 33 192 192 448), lower := (rows 35 14 21 296 112 33 64 128 256), losses := [] }

theorem u1745 : Upper (D 8) (R 8) [34,12,17,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1746 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 296 112 96 193 129 385), lower := (rows 35 14 21 296 112 96 64 128 256), losses := [] }

theorem u1746 : Upper (D 8) (R 8) [34,12,17,288,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1747 : Route 9 := (fun mask => (mask,id))

def c1747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1747 : Upper (D 8) (R 8) [34,12,17,288,96,128] 13 := by
  apply FastRouting.sound _ _ [34,12,17,288,96,128] 13 (by decide) (choices 1) [1,128] r1747 c1747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u247
  · exact u248

def b1748 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 21 296 208 33 224 224 480), lower := (rows 35 14 21 296 208 33 64 128 256), losses := [] }

theorem u1748 : Upper (D 8) (R 8) [34,12,17,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1749 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 21 296 208 96 225 161 417), lower := (rows 35 14 21 296 208 96 64 128 256), losses := [] }

theorem u1749 : Upper (D 8) (R 8) [34,12,17,288,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1750 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 21 328 176 33 224 224 480), lower := (rows 35 14 21 328 176 33 64 128 256), losses := [] }

theorem u1750 : Upper (D 8) (R 8) [34,12,17,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1751 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 148, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 21 328 176 96 225 161 417), lower := (rows 35 14 21 328 176 96 64 128 256), losses := [] }

theorem u1751 : Upper (D 8) (R 8) [34,12,17,320,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1752 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 21 328 176 160 97 225 353), lower := (rows 35 14 21 328 176 160 64 128 256), losses := [] }

theorem u1752 : Upper (D 8) (R 8) [34,12,17,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1753 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 73 400 33 224 224 480), lower := (rows 35 14 52 73 400 33 64 128 256), losses := [] }

theorem u1753 : Upper (D 8) (R 8) [34,12,48,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1754 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 52 73 400 96 225 161 417), lower := (rows 35 14 52 73 400 96 64 128 256), losses := [] }

theorem u1754 : Upper (D 8) (R 8) [34,12,48,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1755 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 52 73 400 160 97 225 353), lower := (rows 35 14 52 73 400 160 64 128 256), losses := [] }

theorem u1755 : Upper (D 8) (R 8) [34,12,48,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1756 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 52 200 273 33 224 224 480), lower := (rows 35 14 52 200 273 33 64 128 256), losses := [] }

theorem u1756 : Upper (D 8) (R 8) [34,12,48,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1757 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 52 200 273 96 225 161 417), lower := (rows 35 14 52 200 273 96 64 128 256), losses := [] }

theorem u1757 : Upper (D 8) (R 8) [34,12,48,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1758 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 52 265 208 33 224 224 480), lower := (rows 35 14 52 265 208 33 64 128 256), losses := [] }

theorem u1758 : Upper (D 8) (R 8) [34,12,48,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1759 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 52 265 208 96 225 161 417), lower := (rows 35 14 52 265 208 96 64 128 256), losses := [] }

theorem u1759 : Upper (D 8) (R 8) [34,12,48,257,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1760 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 52 328 145 33 224 224 480), lower := (rows 35 14 52 328 145 33 64 128 256), losses := [] }

theorem u1760 : Upper (D 8) (R 8) [34,12,48,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1761 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 148, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 52 328 145 96 225 161 417), lower := (rows 35 14 52 328 145 96 64 128 256), losses := [] }

theorem u1761 : Upper (D 8) (R 8) [34,12,48,320,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1762 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 52 328 145 160 97 225 353), lower := (rows 35 14 52 328 145 160 64 128 256), losses := [] }

theorem u1762 : Upper (D 8) (R 8) [34,12,48,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1763 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 152 304 33 224 224 480), lower := (rows 35 14 69 152 304 33 64 128 256), losses := [] }

theorem u1763 : Upper (D 8) (R 8) [34,12,65,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1764 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 152 304 96 225 161 417), lower := (rows 35 14 69 152 304 96 64 128 256), losses := [] }

theorem u1764 : Upper (D 8) (R 8) [34,12,65,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1765 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 69 152 304 160 97 225 353), lower := (rows 35 14 69 152 304 160 64 128 256), losses := [] }

theorem u1765 : Upper (D 8) (R 8) [34,12,65,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1766 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 168 112 33 464 400 400), lower := (rows 35 14 69 168 112 33 64 128 256), losses := [] }

theorem u1766 : Upper (D 8) (R 8) [34,12,65,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1766 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1767 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 35 14 69 168 112 48 449 385 385), lower := (rows 35 14 69 168 112 48 64 128 256), losses := [] }

theorem u1767 : Upper (D 8) (R 8) [34,12,65,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1767 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1768 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 168 112 160 337 401 273), lower := (rows 35 14 69 168 112 160 64 128 256), losses := [] }

theorem u1768 : Upper (D 8) (R 8) [34,12,65,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1769 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 14 69 168 112 288 209 145 401), lower := (rows 35 14 69 168 112 288 64 128 256), losses := [] }

theorem u1769 : Upper (D 8) (R 8) [34,12,65,160,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1769 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1770 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 168 208 33 368 432 304), lower := (rows 35 14 69 168 208 33 64 128 256), losses := [] }

theorem u1770 : Upper (D 8) (R 8) [34,12,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1771 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 14 69 168 208 48 353 417 289), lower := (rows 35 14 69 168 208 48 64 128 256), losses := [] }

theorem u1771 : Upper (D 8) (R 8) [34,12,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1771 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1772 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 14 69 168 208 288 113 177 305), lower := (rows 35 14 69 168 208 288 64 128 256), losses := [] }

theorem u1772 : Upper (D 8) (R 8) [34,12,65,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1772 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1773 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 168 304 33 208 208 464), lower := (rows 35 14 69 168 304 33 64 128 256), losses := [] }

theorem u1773 : Upper (D 8) (R 8) [34,12,65,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1774 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 14 69 168 304 48 193 193 449), lower := (rows 35 14 69 168 304 48 64 128 256), losses := [] }

theorem u1774 : Upper (D 8) (R 8) [34,12,65,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1774 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1775 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 168 304 96 209 145 401), lower := (rows 35 14 69 168 304 96 64 128 256), losses := [] }

theorem u1775 : Upper (D 8) (R 8) [34,12,65,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1776 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 168 304 160 81 209 337), lower := (rows 35 14 69 168 304 160 64 128 256), losses := [] }

theorem u1776 : Upper (D 8) (R 8) [34,12,65,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1777 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 168 336 33 240 176 432), lower := (rows 35 14 69 168 336 33 64 128 256), losses := [] }

theorem u1777 : Upper (D 8) (R 8) [34,12,65,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1778 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 14 69 168 336 48 225 161 417), lower := (rows 35 14 69 168 336 48 64 128 256), losses := [] }

theorem u1778 : Upper (D 8) (R 8) [34,12,65,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1778 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1779 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 168 336 160 113 177 305), lower := (rows 35 14 69 168 336 160 64 128 256), losses := [] }

theorem u1779 : Upper (D 8) (R 8) [34,12,65,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1780 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 168 400 33 112 240 368), lower := (rows 35 14 69 168 400 33 64 128 256), losses := [] }

theorem u1780 : Upper (D 8) (R 8) [34,12,65,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1781 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 14 69 168 400 48 97 225 353), lower := (rows 35 14 69 168 400 48 64 128 256), losses := [] }

theorem u1781 : Upper (D 8) (R 8) [34,12,65,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1781 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1782 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 168 400 96 113 177 305), lower := (rows 35 14 69 168 400 96 64 128 256), losses := [] }

theorem u1782 : Upper (D 8) (R 8) [34,12,65,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1783 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 280 176 33 224 224 480), lower := (rows 35 14 69 280 176 33 64 128 256), losses := [] }

theorem u1783 : Upper (D 8) (R 8) [34,12,65,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1784 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 280 176 96 225 161 417), lower := (rows 35 14 69 280 176 96 64 128 256), losses := [] }

theorem u1784 : Upper (D 8) (R 8) [34,12,65,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1785 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 280 176 160 97 225 353), lower := (rows 35 14 69 280 176 160 64 128 256), losses := [] }

theorem u1785 : Upper (D 8) (R 8) [34,12,65,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1786 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 296 112 33 208 144 400), lower := (rows 35 14 69 296 112 33 64 128 256), losses := [] }

theorem u1786 : Upper (D 8) (R 8) [34,12,65,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1787 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 14 69 296 112 48 193 129 385), lower := (rows 35 14 69 296 112 48 64 128 256), losses := [] }

theorem u1787 : Upper (D 8) (R 8) [34,12,65,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1787 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1788 : Route 9 := (fun mask => (mask,id))

def c1788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1788 : Upper (D 8) (R 8) [34,12,65,288,96,128] 13 := by
  apply FastRouting.sound _ _ [34,12,65,288,96,128] 13 (by decide) (choices 1) [1,16,128] r1788 c1788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u249
  · exact u250
  · exact u251

def b1789 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 296 176 33 208 208 464), lower := (rows 35 14 69 296 176 33 64 128 256), losses := [] }

theorem u1789 : Upper (D 8) (R 8) [34,12,65,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1790 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 14 69 296 176 48 193 193 449), lower := (rows 35 14 69 296 176 48 64 128 256), losses := [] }

theorem u1790 : Upper (D 8) (R 8) [34,12,65,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1790 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1791 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 296 176 96 209 145 401), lower := (rows 35 14 69 296 176 96 64 128 256), losses := [] }

theorem u1791 : Upper (D 8) (R 8) [34,12,65,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1792 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 296 176 160 81 209 337), lower := (rows 35 14 69 296 176 160 64 128 256), losses := [] }

theorem u1792 : Upper (D 8) (R 8) [34,12,65,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1793 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 296 208 33 240 176 432), lower := (rows 35 14 69 296 208 33 64 128 256), losses := [] }

theorem u1793 : Upper (D 8) (R 8) [34,12,65,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1794 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 14 69 296 208 48 225 161 417), lower := (rows 35 14 69 296 208 48 64 128 256), losses := [] }

theorem u1794 : Upper (D 8) (R 8) [34,12,65,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1794 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1795 : Route 9 := (fun mask => (mask,id))

def c1795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1795 : Upper (D 8) (R 8) [34,12,65,288,192,128] 13 := by
  apply FastRouting.sound _ _ [34,12,65,288,192,128] 13 (by decide) (choices 1) [1,16,32] r1795 c1795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u252
  · exact u253
  · exact u254

def b1796 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 392 112 33 240 176 432), lower := (rows 35 14 69 392 112 33 64 128 256), losses := [] }

theorem u1796 : Upper (D 8) (R 8) [34,12,65,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1797 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 14 69 392 112 48 225 161 417), lower := (rows 35 14 69 392 112 48 64 128 256), losses := [] }

theorem u1797 : Upper (D 8) (R 8) [34,12,65,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1797 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1798 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 84, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 69 392 112 160 113 177 305), lower := (rows 35 14 69 392 112 160 64 128 256), losses := [] }

theorem u1798 : Upper (D 8) (R 8) [34,12,65,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1799 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 392 176 33 112 240 368), lower := (rows 35 14 69 392 176 33 64 128 256), losses := [] }

theorem u1799 : Upper (D 8) (R 8) [34,12,65,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1799
end Delivery.IrregularNine14.P08
