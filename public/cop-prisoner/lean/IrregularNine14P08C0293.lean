import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0108

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17580 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 38 73 152 244 212 212 468), lower := (rows 289 35 38 73 152 32 64 128 256), losses := [] }

theorem u17580 : Upper (D 8) (R 8) [288,33,34,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17581 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 38 73 208 188 220 156 412), lower := (rows 289 35 38 73 208 32 64 128 256), losses := [] }

theorem u17581 : Upper (D 8) (R 8) [288,33,34,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17582 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 38 76 152 241 209 209 465), lower := (rows 289 35 38 76 152 32 64 128 256), losses := [] }

theorem u17582 : Upper (D 8) (R 8) [288,33,34,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17583 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 38 76 208 185 217 153 409), lower := (rows 289 35 38 76 208 32 64 128 256), losses := [] }

theorem u17583 : Upper (D 8) (R 8) [288,33,34,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17584 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 38 88 152 229 197 197 453), lower := (rows 289 35 38 88 152 32 64 128 256), losses := [] }

theorem u17584 : Upper (D 8) (R 8) [288,33,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17585 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 73 82 180 212 148 404), lower := (rows 289 35 44 73 82 32 64 128 256), losses := [] }

theorem u17585 : Upper (D 8) (R 8) [288,33,40,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17586 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 73 146 244 212 212 468), lower := (rows 289 35 44 73 146 32 64 128 256), losses := [] }

theorem u17586 : Upper (D 8) (R 8) [288,33,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17587 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 73 148 242 210 210 466), lower := (rows 289 35 44 73 148 32 64 128 256), losses := [] }

theorem u17587 : Upper (D 8) (R 8) [288,33,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17588 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 73 208 182 214 150 406), lower := (rows 289 35 44 73 208 32 64 128 256), losses := [] }

theorem u17588 : Upper (D 8) (R 8) [288,33,40,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17588 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17589 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 74 81 180 212 148 404), lower := (rows 289 35 44 74 81 32 64 128 256), losses := [] }

theorem u17589 : Upper (D 8) (R 8) [288,33,40,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17590 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 74 145 244 212 212 468), lower := (rows 289 35 44 74 145 32 64 128 256), losses := [] }

theorem u17590 : Upper (D 8) (R 8) [288,33,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17591 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 74 148 241 209 209 465), lower := (rows 289 35 44 74 148 32 64 128 256), losses := [] }

theorem u17591 : Upper (D 8) (R 8) [288,33,40,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17592 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 74 208 181 213 149 405), lower := (rows 289 35 44 74 208 32 64 128 256), losses := [] }

theorem u17592 : Upper (D 8) (R 8) [288,33,40,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17593 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 76 145 242 210 210 466), lower := (rows 289 35 44 76 145 32 64 128 256), losses := [] }

theorem u17593 : Upper (D 8) (R 8) [288,33,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17594 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 76 146 241 209 209 465), lower := (rows 289 35 44 76 146 32 64 128 256), losses := [] }

theorem u17594 : Upper (D 8) (R 8) [288,33,40,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17595 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 88 145 230 198 198 454), lower := (rows 289 35 44 88 145 32 64 128 256), losses := [] }

theorem u17595 : Upper (D 8) (R 8) [288,33,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17596 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 88 146 229 197 197 453), lower := (rows 289 35 44 88 146 32 64 128 256), losses := [] }

theorem u17596 : Upper (D 8) (R 8) [288,33,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17597 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 88 148 227 195 195 451), lower := (rows 289 35 44 88 148 32 64 128 256), losses := [] }

theorem u17597 : Upper (D 8) (R 8) [288,33,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17598 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 200 81 182 214 150 406), lower := (rows 289 35 44 200 81 32 64 128 256), losses := [] }

theorem u17598 : Upper (D 8) (R 8) [288,33,40,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17599 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 44 200 82 181 213 149 405), lower := (rows 289 35 44 200 82 32 64 128 256), losses := [] }

theorem u17599 : Upper (D 8) (R 8) [288,33,40,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17600 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 74 148 184 248 184 440), lower := (rows 289 35 69 74 148 32 64 128 256), losses := [] }

theorem u17600 : Upper (D 8) (R 8) [288,33,65,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17601 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 74 152 180 244 180 436), lower := (rows 289 35 69 74 152 32 64 128 256), losses := [] }

theorem u17601 : Upper (D 8) (R 8) [288,33,65,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17602 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 74 176 188 220 156 412), lower := (rows 289 35 69 74 176 32 64 128 256), losses := [] }

theorem u17602 : Upper (D 8) (R 8) [288,33,65,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17603 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 88 146 172 236 172 428), lower := (rows 289 35 69 88 146 32 64 128 256), losses := [] }

theorem u17603 : Upper (D 8) (R 8) [288,33,65,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17604 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 88 176 174 206 142 398), lower := (rows 289 35 69 88 176 32 64 128 256), losses := [] }

theorem u17604 : Upper (D 8) (R 8) [288,33,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17605 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 104 146 188 220 156 412), lower := (rows 289 35 69 104 146 32 64 128 256), losses := [] }

theorem u17605 : Upper (D 8) (R 8) [288,33,65,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17606 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 104 148 186 218 154 410), lower := (rows 289 35 69 104 148 32 64 128 256), losses := [] }

theorem u17606 : Upper (D 8) (R 8) [288,33,65,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17607 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 104 152 182 214 150 406), lower := (rows 289 35 69 104 152 32 64 128 256), losses := [] }

theorem u17607 : Upper (D 8) (R 8) [288,33,65,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17608 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 138 148 120 120 248 376), lower := (rows 289 35 69 138 148 32 64 128 256), losses := [] }

theorem u17608 : Upper (D 8) (R 8) [288,33,65,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17609 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 138 176 124 92 220 348), lower := (rows 289 35 69 138 176 32 64 128 256), losses := [] }

theorem u17609 : Upper (D 8) (R 8) [288,33,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17610 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 138 208 60 124 188 316), lower := (rows 289 35 69 138 208 32 64 128 256), losses := [] }

theorem u17610 : Upper (D 8) (R 8) [288,33,65,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17611 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 140 176 122 90 218 346), lower := (rows 289 35 69 140 176 32 64 128 256), losses := [] }

theorem u17611 : Upper (D 8) (R 8) [288,33,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17612 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 140 208 58 122 186 314), lower := (rows 289 35 69 140 208 32 64 128 256), losses := [] }

theorem u17612 : Upper (D 8) (R 8) [288,33,65,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17613 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 69 168 208 62 94 158 286), lower := (rows 289 35 69 168 208 32 64 128 256), losses := [] }

theorem u17613 : Upper (D 8) (R 8) [288,33,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17614 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 70 88 176 173 205 141 397), lower := (rows 289 35 70 88 176 32 64 128 256), losses := [] }

theorem u17614 : Upper (D 8) (R 8) [288,33,66,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17615 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 70 104 148 185 217 153 409), lower := (rows 289 35 70 104 148 32 64 128 256), losses := [] }

theorem u17615 : Upper (D 8) (R 8) [288,33,66,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17616 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 70 104 152 181 213 149 405), lower := (rows 289 35 70 104 152 32 64 128 256), losses := [] }

theorem u17616 : Upper (D 8) (R 8) [288,33,66,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17617 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 70 140 176 121 89 217 345), lower := (rows 289 35 70 140 176 32 64 128 256), losses := [] }

theorem u17617 : Upper (D 8) (R 8) [288,33,66,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17618 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 70 140 208 57 121 185 313), lower := (rows 289 35 70 140 208 32 64 128 256), losses := [] }

theorem u17618 : Upper (D 8) (R 8) [288,33,66,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17619 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 70 168 208 61 93 157 285), lower := (rows 289 35 70 168 208 32 64 128 256), losses := [] }

theorem u17619 : Upper (D 8) (R 8) [288,33,66,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17620 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 76 168 208 55 87 151 279), lower := (rows 289 35 76 168 208 32 64 128 256), losses := [] }

theorem u17620 : Upper (D 8) (R 8) [288,33,72,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17621 : PairBound 9 := { available := 216, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 38 73 145 248 216 216 472), lower := (rows 289 38 38 73 145 32 64 128 256), losses := [] }

theorem u17621 : Upper (D 8) (R 8) [288,36,34,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17622 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 38 73 152 241 209 209 465), lower := (rows 289 38 38 73 152 32 64 128 256), losses := [] }

theorem u17622 : Upper (D 8) (R 8) [288,36,34,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17623 : PairBound 9 := { available := 153, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 38 73 208 185 217 153 409), lower := (rows 289 38 38 73 208 32 64 128 256), losses := [] }

theorem u17623 : Upper (D 8) (R 8) [288,36,34,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17624 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 38 88 152 225 193 193 449), lower := (rows 289 38 38 88 152 32 64 128 256), losses := [] }

theorem u17624 : Upper (D 8) (R 8) [288,36,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17625 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 73 82 177 209 145 401), lower := (rows 289 38 44 73 82 32 64 128 256), losses := [] }

theorem u17625 : Upper (D 8) (R 8) [288,36,40,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17626 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 73 145 242 210 210 466), lower := (rows 289 38 44 73 145 32 64 128 256), losses := [] }

theorem u17626 : Upper (D 8) (R 8) [288,36,40,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17627 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 73 146 241 209 209 465), lower := (rows 289 38 44 73 146 32 64 128 256), losses := [] }

theorem u17627 : Upper (D 8) (R 8) [288,36,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17628 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 73 208 179 211 147 403), lower := (rows 289 38 44 73 208 32 64 128 256), losses := [] }

theorem u17628 : Upper (D 8) (R 8) [288,36,40,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17629 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 74 81 177 209 145 401), lower := (rows 289 38 44 74 81 32 64 128 256), losses := [] }

theorem u17629 : Upper (D 8) (R 8) [288,36,40,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17630 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 74 145 241 209 209 465), lower := (rows 289 38 44 74 145 32 64 128 256), losses := [] }

theorem u17630 : Upper (D 8) (R 8) [288,36,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17631 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 74 208 177 209 145 401), lower := (rows 289 38 44 74 208 32 64 128 256), losses := [] }

theorem u17631 : Upper (D 8) (R 8) [288,36,40,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17632 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 88 145 227 195 195 451), lower := (rows 289 38 44 88 145 32 64 128 256), losses := [] }

theorem u17632 : Upper (D 8) (R 8) [288,36,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17633 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 88 146 225 193 193 449), lower := (rows 289 38 44 88 146 32 64 128 256), losses := [] }

theorem u17633 : Upper (D 8) (R 8) [288,36,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17634 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 200 81 179 211 147 403), lower := (rows 289 38 44 200 81 32 64 128 256), losses := [] }

theorem u17634 : Upper (D 8) (R 8) [288,36,40,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17635 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 200 82 177 209 145 401), lower := (rows 289 38 44 200 82 32 64 128 256), losses := [] }

theorem u17635 : Upper (D 8) (R 8) [288,36,40,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17636 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 38 69 56 81 170 202 138 394), lower := (rows 289 38 69 56 81 32 64 128 256), losses := [] }

theorem u17636 : Upper (D 8) (R 8) [288,36,65,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17637 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 56 82 169 201 137 393), lower := (rows 289 38 69 56 82 32 64 128 256), losses := [] }

theorem u17637 : Upper (D 8) (R 8) [288,36,65,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17638 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 56 88 163 195 131 387), lower := (rows 289 38 69 56 88 32 64 128 256), losses := [] }

theorem u17638 : Upper (D 8) (R 8) [288,36,65,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17639_8 : Upper (D 8) (R 8) [288,36,65,48,129,8] 13 :=
  permutation_upper _ _ _ [288,36,65,48,129,2] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6494

theorem m17639_128 : Upper (D 8) (R 8) [288,36,65,48,129,128] 13 :=
  permutation_upper _ _ _ [288,36,65,48,129,64] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6495

def r17639 : Route 9 := (fun mask => (mask,id))

def c17639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17639 : Upper (D 8) (R 8) [288,36,65,48,129] 13 := by
  apply FastRouting.sound _ _ [288,36,65,48,129] 13 (by decide) (choices 1) [2,8,64,128] r17639 c17639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6494
  · exact m17639_8
  · exact u6495
  · exact m17639_128

#print axioms u17639
end Delivery.IrregularNine14.P08
