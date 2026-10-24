import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b660 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 113 146 164 266 17 40 69 197 325), lower := (rows 113 146 164 266 17 40 64 128 256), losses := [] }

theorem u660 : Upper (D 0) (R 0) [112,144,160,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b660
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 164 266 17 96 77 141 269), lower := (rows 113 146 164 266 17 96 64 128 256), losses := [] }

theorem u661 : Upper (D 0) (R 0) [112,144,160,258,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b661
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 146 164 328 17 33 78 142 270), lower := (rows 113 146 164 328 17 33 64 128 256), losses := [] }

theorem u662 : Upper (D 0) (R 0) [112,144,160,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b662
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 113 146 164 328 17 34 77 141 269), lower := (rows 113 146 164 328 17 34 64 128 256), losses := [] }

theorem u663 : Upper (D 0) (R 0) [112,144,160,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b663
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 113 146 164 328 17 36 75 139 267), lower := (rows 113 146 164 328 17 36 64 128 256), losses := [] }

theorem u664 : Upper (D 0) (R 0) [112,144,160,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b664
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 113 146 164 328 17 40 71 135 263), lower := (rows 113 146 164 328 17 40 64 128 256), losses := [] }

theorem u665 : Upper (D 0) (R 0) [112,144,160,320,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b665
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 263 11 52 88 144 33 224 224 480), lower := (rows 263 11 52 88 144 33 64 128 256), losses := [] }

theorem u666 : Upper (D 0) (R 0) [262,9,48,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b666
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 263 11 52 88 144 96 225 161 417), lower := (rows 263 11 52 88 144 96 64 128 256), losses := [] }

theorem u667 : Upper (D 0) (R 0) [262,9,48,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b667
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 263 11 52 88 144 160 97 225 353), lower := (rows 263 11 52 88 144 160 64 128 256), losses := [] }

theorem u668 : Upper (D 0) (R 0) [262,9,48,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b668
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b669 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 263 11 52 200 17 96 240 176 432), lower := (rows 263 11 52 200 17 96 64 128 256), losses := [] }

theorem u669 : Upper (D 0) (R 0) [262,9,48,192,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b669
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b670 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 263 11 52 200 48 96 209 145 401), lower := (rows 263 11 52 200 48 96 64 128 256), losses := [] }

theorem u670 : Upper (D 0) (R 0) [262,9,48,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b670
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 52, targets := 1 }], pairs := [(2,0)], upper := (rows 263 11 52 200 80 160 113 177 305), lower := (rows 263 11 52 200 80 160 64 128 256), losses := [] }

theorem u671 : Upper (D 0) (R 0) [262,9,48,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b671
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b672 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 44 88 144 33 224 224 480), lower := (rows 263 19 44 88 144 33 64 128 256), losses := [] }

theorem u672 : Upper (D 0) (R 0) [262,17,40,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b672
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 44 88 144 96 225 161 417), lower := (rows 263 19 44 88 144 96 64 128 256), losses := [] }

theorem u673 : Upper (D 0) (R 0) [262,17,40,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b673
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 97, camps := [], pairs := [(2,0)], upper := (rows 263 19 44 88 144 160 97 225 353), lower := (rows 263 19 44 88 144 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 176 176 64 128 256), good := (rows 262 50 60 124 176 176 64 176 256) }] }

theorem u674 : Upper (D 0) (R 0) [262,17,40,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b674
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 44 200 80 33 240 176 432), lower := (rows 263 19 44 200 80 33 64 128 256), losses := [] }

theorem u675 : Upper (D 0) (R 0) [262,17,40,192,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b675
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 52, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 44 200 80 48 225 161 417), lower := (rows 263 19 44 200 80 48 64 128 256), losses := [] }

theorem u676 : Upper (D 0) (R 0) [262,17,40,192,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b676
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b677 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 263 19 44 200 80 160 113 177 305), lower := (rows 263 19 44 200 80 160 64 128 256), losses := [] }

theorem u677 : Upper (D 0) (R 0) [262,17,40,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b677
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b678 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 263 19 100 56 144 33 200 200 456), lower := (rows 263 19 100 56 144 33 64 128 256), losses := [] }

theorem u678 : Upper (D 0) (R 0) [262,17,96,48,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b678
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b679 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 263 19 100 56 144 40 193 193 449), lower := (rows 263 19 100 56 144 40 64 128 256), losses := [] }

theorem u679 : Upper (D 0) (R 0) [262,17,96,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b679
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b680 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 263 19 100 56 144 96 201 137 393), lower := (rows 263 19 100 56 144 96 64 128 256), losses := [] }

theorem u680 : Upper (D 0) (R 0) [262,17,96,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b680
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b681 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 263 19 100 56 144 160 73 201 329), lower := (rows 263 19 100 56 144 160 64 128 256), losses := [] }

theorem u681 : Upper (D 0) (R 0) [262,17,96,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b681
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b682 : PairBound 9 := { available := 88, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 100 168 144 33 88 216 344), lower := (rows 263 19 100 168 144 33 64 128 256), losses := [] }

theorem u682 : Upper (D 0) (R 0) [262,17,96,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b682
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b683 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 263 19 100 168 144 40 81 209 337), lower := (rows 263 19 100 168 144 40 64 128 256), losses := [] }

theorem u683 : Upper (D 0) (R 0) [262,17,96,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b683
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b684 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 263 19 100 168 144 48 73 201 329), lower := (rows 263 19 100 168 144 48 64 128 256), losses := [] }

theorem u684 : Upper (D 0) (R 0) [262,17,96,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b684
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 263 19 100 168 144 96 89 153 281), lower := (rows 263 19 100 168 144 96 64 128 256), losses := [] }

theorem u685 : Upper (D 0) (R 0) [262,17,96,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b685
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 263 26 100 137 48 33 208 208 464), lower := (rows 263 26 100 137 48 33 64 128 256), losses := [] }

theorem u686 : Upper (D 0) (R 0) [262,24,96,129,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b686
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0)], upper := (rows 263 26 100 137 48 48 193 193 449), lower := (rows 263 26 100 137 48 48 64 128 256), losses := [] }

theorem u687 : Upper (D 0) (R 0) [262,24,96,129,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b687
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b688 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 263 26 100 137 48 96 209 145 401), lower := (rows 263 26 100 137 48 96 64 128 256), losses := [] }

theorem u688 : Upper (D 0) (R 0) [262,24,96,129,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b688
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b689 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0)], upper := (rows 263 26 100 137 48 160 81 209 337), lower := (rows 263 26 100 137 48 160 64 128 256), losses := [] }

theorem u689 : Upper (D 0) (R 0) [262,24,96,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b689
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b690 : PairBound 9 := { available := 208, camps := [], pairs := [(1,5)], upper := (rows 263 26 100 168 17 33 208 208 464), lower := (rows 263 26 100 168 17 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 49 0 127 191 319), good := (rows 471 474 468 474 465 465 64 128 256) }] }

theorem u690 : Upper (D 0) (R 0) [262,24,96,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b690
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b691 : PairBound 9 := { available := 193, camps := [], pairs := [(2,4)], upper := (rows 263 26 100 168 17 48 193 193 449), lower := (rows 263 26 100 168 17 48 64 128 256), losses := [{ target := 4, region := (rows 1 2 36 40 0 32 81 145 273), good := (rows 455 458 108 172 449 492 64 128 256) }] }

theorem u691 : Upper (D 0) (R 0) [262,24,96,160,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b691
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b692 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 263 26 100 168 17 96 209 145 401), lower := (rows 263 26 100 168 17 96 64 128 256), losses := [] }

theorem u692 : Upper (D 0) (R 0) [262,24,96,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b692
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b693 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 263 26 100 168 17 160 81 209 337), lower := (rows 263 26 100 168 17 160 64 128 256), losses := [] }

theorem u693 : Upper (D 0) (R 0) [262,24,96,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b693
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 145, camps := [], pairs := [(1,5)], upper := (rows 263 26 100 168 80 33 209 145 401), lower := (rows 263 26 100 168 80 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 125 0 97 161 289), good := (rows 471 26 468 474 80 465 80 128 256) }] }

theorem u694 : Upper (D 0) (R 0) [262,24,96,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b694
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b695 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 263 26 100 168 80 48 193 129 385), lower := (rows 263 26 100 168 80 48 64 128 256), losses := [] }

theorem u695 : Upper (D 0) (R 0) [262,24,96,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b695
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b696 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 263 26 100 168 80 160 81 145 273), lower := (rows 263 26 100 168 80 160 64 128 256), losses := [] }

theorem u696 : Upper (D 0) (R 0) [262,24,96,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b696
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b697 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 196 88 17 33 232 168 424), lower := (rows 263 50 196 88 17 33 64 128 256), losses := [] }

theorem u697 : Upper (D 0) (R 0) [262,48,192,80,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b697
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b698 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 263 50 196 88 17 40 225 161 417), lower := (rows 263 50 196 88 17 40 64 128 256), losses := [] }

theorem u698 : Upper (D 0) (R 0) [262,48,192,80,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b698
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b699 : PairBound 9 := { available := 41, camps := [], pairs := [(1,6)], upper := (rows 263 50 196 88 17 160 105 169 297), lower := (rows 263 50 196 88 17 160 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 17 164 0 128 256), good := (rows 311 50 164 24 19 160 0 160 256) }] }

theorem u699 : Upper (D 0) (R 0) [262,48,192,80,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b699
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b700 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 44 88 144 33 224 224 480), lower := (rows 275 7 44 88 144 33 64 128 256), losses := [] }

theorem u700 : Upper (D 0) (R 0) [274,5,40,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b700
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 44 88 144 96 225 161 417), lower := (rows 275 7 44 88 144 96 64 128 256), losses := [] }

theorem u701 : Upper (D 0) (R 0) [274,5,40,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b701
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b702 : PairBound 9 := { available := 97, camps := [], pairs := [(2,0)], upper := (rows 275 7 44 88 144 160 97 225 353), lower := (rows 275 7 44 88 144 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 176 176 64 128 256), good := (rows 306 6 60 124 176 176 64 176 256) }] }

theorem u702 : Upper (D 0) (R 0) [274,5,40,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b702
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b703 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 44 200 80 33 240 176 432), lower := (rows 275 7 44 200 80 33 64 128 256), losses := [] }

theorem u703 : Upper (D 0) (R 0) [274,5,40,192,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b703
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 52, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 44 200 80 48 225 161 417), lower := (rows 275 7 44 200 80 48 64 128 256), losses := [] }

theorem u704 : Upper (D 0) (R 0) [274,5,40,192,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b704
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 275 7 44 200 80 160 113 177 305), lower := (rows 275 7 44 200 80 160 64 128 256), losses := [] }

theorem u705 : Upper (D 0) (R 0) [274,5,40,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b705
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 275 7 100 56 144 33 200 200 456), lower := (rows 275 7 100 56 144 33 64 128 256), losses := [] }

theorem u706 : Upper (D 0) (R 0) [274,5,96,48,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b706
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 7 100 56 144 40 193 193 449), lower := (rows 275 7 100 56 144 40 64 128 256), losses := [] }

theorem u707 : Upper (D 0) (R 0) [274,5,96,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b707
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 275 7 100 56 144 96 201 137 393), lower := (rows 275 7 100 56 144 96 64 128 256), losses := [] }

theorem u708 : Upper (D 0) (R 0) [274,5,96,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b708
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 275 7 100 56 144 160 73 201 329), lower := (rows 275 7 100 56 144 160 64 128 256), losses := [] }

theorem u709 : Upper (D 0) (R 0) [274,5,96,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b709
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 88, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 275 7 100 168 144 33 88 216 344), lower := (rows 275 7 100 168 144 33 64 128 256), losses := [] }

theorem u710 : Upper (D 0) (R 0) [274,5,96,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b710
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 275 7 100 168 144 40 81 209 337), lower := (rows 275 7 100 168 144 40 64 128 256), losses := [] }

theorem u711 : Upper (D 0) (R 0) [274,5,96,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b711
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 275 7 100 168 144 48 73 201 329), lower := (rows 275 7 100 168 144 48 64 128 256), losses := [] }

theorem u712 : Upper (D 0) (R 0) [274,5,96,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b712
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b713 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 275 7 100 168 144 96 89 153 281), lower := (rows 275 7 100 168 144 96 64 128 256), losses := [] }

theorem u713 : Upper (D 0) (R 0) [274,5,96,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b713
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b714 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 275 14 37 73 144 48 224 224 480), lower := (rows 275 14 37 73 144 48 64 128 256), losses := [] }

theorem u714 : Upper (D 0) (R 0) [274,12,33,65,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b714
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b715 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 38, targets := 16 }], pairs := [(1,4)], upper := (rows 275 14 37 73 144 96 240 176 432), lower := (rows 275 14 37 73 144 96 64 128 256), losses := [] }

theorem u715 : Upper (D 0) (R 0) [274,12,33,65,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b715
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 112, camps := [], pairs := [(1,4)], upper := (rows 275 14 37 73 144 160 112 240 368), lower := (rows 275 14 37 73 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 10 5 8 0 176 64 128 256), good := (rows 295 14 37 79 160 160 64 160 256) }] }

theorem u716 : Upper (D 0) (R 0) [274,12,33,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b716
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b717 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 28 104 144 33 196 196 452), lower := (rows 275 35 28 104 144 33 64 128 256), losses := [] }

theorem u717 : Upper (D 0) (R 0) [274,33,24,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b717
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b718 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 35 28 104 144 36 193 193 449), lower := (rows 275 35 28 104 144 36 64 128 256), losses := [] }

theorem u718 : Upper (D 0) (R 0) [274,33,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b718
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b719 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 275 35 28 104 144 96 197 133 389), lower := (rows 275 35 28 104 144 96 64 128 256), losses := [] }

theorem u719 : Upper (D 0) (R 0) [274,33,24,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b719
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P00
