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

def b1680 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 7 196 88 176 288 105 169 297), lower := (rows 35 7 196 88 176 288 64 128 256), losses := [] }

theorem u1680 : Upper (D 8) (R 8) [34,5,192,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1680 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1681 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 88 304 33 232 168 424), lower := (rows 35 7 196 88 304 33 64 128 256), losses := [] }

theorem u1681 : Upper (D 8) (R 8) [34,5,192,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1682 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 196 88 304 40 225 161 417), lower := (rows 35 7 196 88 304 40 64 128 256), losses := [] }

theorem u1682 : Upper (D 8) (R 8) [34,5,192,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1682 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1683 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 88 304 160 105 169 297), lower := (rows 35 7 196 88 304 160 64 128 256), losses := [] }

theorem u1683 : Upper (D 8) (R 8) [34,5,192,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1684 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 88 400 33 104 168 296), lower := (rows 35 7 196 88 400 33 64 128 256), losses := [] }

theorem u1684 : Upper (D 8) (R 8) [34,5,192,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1685 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 196 88 400 40 97 161 289), lower := (rows 35 7 196 88 400 40 64 128 256), losses := [] }

theorem u1685 : Upper (D 8) (R 8) [34,5,192,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1685 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1686 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 104 176 33 344 408 280), lower := (rows 35 7 196 104 176 33 64 128 256), losses := [] }

theorem u1686 : Upper (D 8) (R 8) [34,5,192,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1687 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 35 7 196 104 176 40 337 401 273), lower := (rows 35 7 196 104 176 40 64 128 256), losses := [] }

theorem u1687 : Upper (D 8) (R 8) [34,5,192,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1687 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1688 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 7 196 104 176 288 89 153 281), lower := (rows 35 7 196 104 176 288 64 128 256), losses := [] }

theorem u1688 : Upper (D 8) (R 8) [34,5,192,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1688 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1689 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 104 280 33 240 176 432), lower := (rows 35 7 196 104 280 33 64 128 256), losses := [] }

theorem u1689 : Upper (D 8) (R 8) [34,5,192,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1690 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 196 104 280 48 225 161 417), lower := (rows 35 7 196 104 280 48 64 128 256), losses := [] }

theorem u1690 : Upper (D 8) (R 8) [34,5,192,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1690 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1691 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 104 280 160 113 177 305), lower := (rows 35 7 196 104 280 160 64 128 256), losses := [] }

theorem u1691 : Upper (D 8) (R 8) [34,5,192,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1692 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 104 304 33 216 152 408), lower := (rows 35 7 196 104 304 33 64 128 256), losses := [] }

theorem u1692 : Upper (D 8) (R 8) [34,5,192,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1693 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 7 196 104 304 40 209 145 401), lower := (rows 35 7 196 104 304 40 64 128 256), losses := [] }

theorem u1693 : Upper (D 8) (R 8) [34,5,192,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1693 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1694 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 7 196 104 304 48 201 137 393), lower := (rows 35 7 196 104 304 48 64 128 256), losses := [] }

theorem u1694 : Upper (D 8) (R 8) [34,5,192,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1694 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1695 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 104 304 160 89 153 281), lower := (rows 35 7 196 104 304 160 64 128 256), losses := [] }

theorem u1695 : Upper (D 8) (R 8) [34,5,192,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1696 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 104 400 33 120 184 312), lower := (rows 35 7 196 104 400 33 64 128 256), losses := [] }

theorem u1696 : Upper (D 8) (R 8) [34,5,192,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1697 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 7 196 104 400 40 113 177 305), lower := (rows 35 7 196 104 400 40 64 128 256), losses := [] }

theorem u1697 : Upper (D 8) (R 8) [34,5,192,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1697 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1698 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 7 196 104 400 48 105 169 297), lower := (rows 35 7 196 104 400 48 64 128 256), losses := [] }

theorem u1698 : Upper (D 8) (R 8) [34,5,192,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1698 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1699 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 56 208 33 224 224 480), lower := (rows 35 7 268 56 208 33 64 128 256), losses := [] }

theorem u1699 : Upper (D 8) (R 8) [34,5,264,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1700 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 56 208 96 225 161 417), lower := (rows 35 7 268 56 208 96 64 128 256), losses := [] }

theorem u1700 : Upper (D 8) (R 8) [34,5,264,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1701 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 88 176 33 224 224 480), lower := (rows 35 7 268 88 176 33 64 128 256), losses := [] }

theorem u1701 : Upper (D 8) (R 8) [34,5,264,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1702 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 268 88 176 96 225 161 417), lower := (rows 35 7 268 88 176 96 64 128 256), losses := [] }

theorem u1702 : Upper (D 8) (R 8) [34,5,264,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1703 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 268 88 176 160 97 225 353), lower := (rows 35 7 268 88 176 160 64 128 256), losses := [] }

theorem u1703 : Upper (D 8) (R 8) [34,5,264,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1704 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 104 176 33 208 208 464), lower := (rows 35 7 268 104 176 33 64 128 256), losses := [] }

theorem u1704 : Upper (D 8) (R 8) [34,5,264,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1705 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 7 268 104 176 48 193 193 449), lower := (rows 35 7 268 104 176 48 64 128 256), losses := [] }

theorem u1705 : Upper (D 8) (R 8) [34,5,264,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1705 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1706 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 104 176 96 209 145 401), lower := (rows 35 7 268 104 176 96 64 128 256), losses := [] }

theorem u1706 : Upper (D 8) (R 8) [34,5,264,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1707 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 268 104 176 160 81 209 337), lower := (rows 35 7 268 104 176 160 64 128 256), losses := [] }

theorem u1707 : Upper (D 8) (R 8) [34,5,264,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1708 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 104 208 33 240 176 432), lower := (rows 35 7 268 104 208 33 64 128 256), losses := [] }

theorem u1708 : Upper (D 8) (R 8) [34,5,264,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1709 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 268 104 208 48 225 161 417), lower := (rows 35 7 268 104 208 48 64 128 256), losses := [] }

theorem u1709 : Upper (D 8) (R 8) [34,5,264,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1709 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1710 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 268 104 208 160 113 177 305), lower := (rows 35 7 268 104 208 160 64 128 256), losses := [] }

theorem u1710 : Upper (D 8) (R 8) [34,5,264,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1711 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 200 112 33 240 176 432), lower := (rows 35 7 268 200 112 33 64 128 256), losses := [] }

theorem u1711 : Upper (D 8) (R 8) [34,5,264,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1712 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 268 200 112 48 225 161 417), lower := (rows 35 7 268 200 112 48 64 128 256), losses := [] }

theorem u1712 : Upper (D 8) (R 8) [34,5,264,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1712 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1713 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 268 200 112 160 113 177 305), lower := (rows 35 7 268 200 112 160 64 128 256), losses := [] }

theorem u1713 : Upper (D 8) (R 8) [34,5,264,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1714 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 56 152 33 224 224 480), lower := (rows 35 7 324 56 152 33 64 128 256), losses := [] }

theorem u1714 : Upper (D 8) (R 8) [34,5,320,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1715 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 56 152 96 225 161 417), lower := (rows 35 7 324 56 152 96 64 128 256), losses := [] }

theorem u1715 : Upper (D 8) (R 8) [34,5,320,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1716 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 324 56 152 160 97 225 353), lower := (rows 35 7 324 56 152 160 64 128 256), losses := [] }

theorem u1716 : Upper (D 8) (R 8) [34,5,320,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1717 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 56 208 33 232 168 424), lower := (rows 35 7 324 56 208 33 64 128 256), losses := [] }

theorem u1717 : Upper (D 8) (R 8) [34,5,320,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1718 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 324 56 208 40 225 161 417), lower := (rows 35 7 324 56 208 40 64 128 256), losses := [] }

theorem u1718 : Upper (D 8) (R 8) [34,5,320,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1718 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1719 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 56 208 160 105 169 297), lower := (rows 35 7 324 56 208 160 64 128 256), losses := [] }

theorem u1719 : Upper (D 8) (R 8) [34,5,320,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1720 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 88 176 33 232 168 424), lower := (rows 35 7 324 88 176 33 64 128 256), losses := [] }

theorem u1720 : Upper (D 8) (R 8) [34,5,320,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1721 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 324 88 176 40 225 161 417), lower := (rows 35 7 324 88 176 40 64 128 256), losses := [] }

theorem u1721 : Upper (D 8) (R 8) [34,5,320,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1721 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1722 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 88 176 160 105 169 297), lower := (rows 35 7 324 88 176 160 64 128 256), losses := [] }

theorem u1722 : Upper (D 8) (R 8) [34,5,320,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1723 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 104 152 33 240 176 432), lower := (rows 35 7 324 104 152 33 64 128 256), losses := [] }

theorem u1723 : Upper (D 8) (R 8) [34,5,320,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1724 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 324 104 152 48 225 161 417), lower := (rows 35 7 324 104 152 48 64 128 256), losses := [] }

theorem u1724 : Upper (D 8) (R 8) [34,5,320,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1724 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1725 : Route 9 := (fun mask => (mask,id))

def c1725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1725 : Upper (D 8) (R 8) [34,5,320,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,5,320,96,136,128] 13 (by decide) (choices 1) [1,16,32] r1725 c1725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u242
  · exact u243
  · exact u244

def b1726 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 104 176 33 216 152 408), lower := (rows 35 7 324 104 176 33 64 128 256), losses := [] }

theorem u1726 : Upper (D 8) (R 8) [34,5,320,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1727 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 7 324 104 176 40 209 145 401), lower := (rows 35 7 324 104 176 40 64 128 256), losses := [] }

theorem u1727 : Upper (D 8) (R 8) [34,5,320,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1727 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1728 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 7 324 104 176 48 201 137 393), lower := (rows 35 7 324 104 176 48 64 128 256), losses := [] }

theorem u1728 : Upper (D 8) (R 8) [34,5,320,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1728 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1729 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 104 176 160 89 153 281), lower := (rows 35 7 324 104 176 160 64 128 256), losses := [] }

theorem u1729 : Upper (D 8) (R 8) [34,5,320,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1730 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 168 208 33 120 184 312), lower := (rows 35 7 324 168 208 33 64 128 256), losses := [] }

theorem u1730 : Upper (D 8) (R 8) [34,5,320,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1731 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 7 324 168 208 40 113 177 305), lower := (rows 35 7 324 168 208 40 64 128 256), losses := [] }

theorem u1731 : Upper (D 8) (R 8) [34,5,320,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1731 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1732 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 7 324 168 208 48 105 169 297), lower := (rows 35 7 324 168 208 48 64 128 256), losses := [] }

theorem u1732 : Upper (D 8) (R 8) [34,5,320,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1732 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1733 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 21 104 176 33 448 448 448), lower := (rows 35 14 21 104 176 33 64 128 256), losses := [] }

theorem u1733 : Upper (D 8) (R 8) [34,12,17,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1734 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 104 176 96 449 385 385), lower := (rows 35 14 21 104 176 96 64 128 256), losses := [] }

theorem u1734 : Upper (D 8) (R 8) [34,12,17,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1735 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 21 104 176 160 321 449 321), lower := (rows 35 14 21 104 176 160 64 128 256), losses := [] }

theorem u1735 : Upper (D 8) (R 8) [34,12,17,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1736 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 14 21 104 176 288 193 193 449), lower := (rows 35 14 21 104 176 288 64 128 256), losses := [] }

theorem u1736 : Upper (D 8) (R 8) [34,12,17,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1736 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1737 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 21 104 304 33 192 192 448), lower := (rows 35 14 21 104 304 33 64 128 256), losses := [] }

theorem u1737 : Upper (D 8) (R 8) [34,12,17,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1738 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 104 304 96 193 129 385), lower := (rows 35 14 21 104 304 96 64 128 256), losses := [] }

theorem u1738 : Upper (D 8) (R 8) [34,12,17,96,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1739 : Route 9 := (fun mask => (mask,id))

def c1739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1739 : Upper (D 8) (R 8) [34,12,17,96,288,128] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96,288,128] 13 (by decide) (choices 1) [1,128] r1739 c1739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u245
  · exact u246

#print axioms u1739
end Delivery.IrregularNine14.P08
