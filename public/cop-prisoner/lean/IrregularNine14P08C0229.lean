import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13740 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 137 208 306 370 434 306), lower := (rows 97 14 37 137 208 32 64 128 256), losses := [] }

theorem u13740 : Upper (D 8) (R 8) [96,12,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13741 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 137 274 240 240 240 496), lower := (rows 97 14 37 137 274 32 64 128 256), losses := [] }

theorem u13741 : Upper (D 8) (R 8) [96,12,33,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13742 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 137 304 242 210 210 466), lower := (rows 97 14 37 137 304 32 64 128 256), losses := [] }

theorem u13742 : Upper (D 8) (R 8) [96,12,33,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13743 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 137 336 178 242 178 434), lower := (rows 97 14 37 137 336 32 64 128 256), losses := [] }

theorem u13743 : Upper (D 8) (R 8) [96,12,33,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13744 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 137 400 114 114 242 370), lower := (rows 97 14 37 137 400 32 64 128 256), losses := [] }

theorem u13744 : Upper (D 8) (R 8) [96,12,33,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13745 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 138 273 240 240 240 496), lower := (rows 97 14 37 138 273 32 64 128 256), losses := [] }

theorem u13745 : Upper (D 8) (R 8) [96,12,33,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13746 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 138 304 241 209 209 465), lower := (rows 97 14 37 138 304 32 64 128 256), losses := [] }

theorem u13746 : Upper (D 8) (R 8) [96,12,33,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13747 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 138 336 177 241 177 433), lower := (rows 97 14 37 138 336 32 64 128 256), losses := [] }

theorem u13747 : Upper (D 8) (R 8) [96,12,33,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13748 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 152 50 481 449 449 449), lower := (rows 97 14 37 152 50 32 64 128 256), losses := [] }

theorem u13748 : Upper (D 8) (R 8) [96,12,33,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13749 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 152 273 226 226 226 482), lower := (rows 97 14 37 152 273 32 64 128 256), losses := [] }

theorem u13749 : Upper (D 8) (R 8) [96,12,33,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13750 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 152 274 225 225 225 481), lower := (rows 97 14 37 152 274 32 64 128 256), losses := [] }

theorem u13750 : Upper (D 8) (R 8) [96,12,33,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13751 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 152 304 227 195 195 451), lower := (rows 97 14 37 152 304 32 64 128 256), losses := [] }

theorem u13751 : Upper (D 8) (R 8) [96,12,33,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13752 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 152 336 163 227 163 419), lower := (rows 97 14 37 152 336 32 64 128 256), losses := [] }

theorem u13752 : Upper (D 8) (R 8) [96,12,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13753 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 168 82 433 465 401 401), lower := (rows 97 14 37 168 82 32 64 128 256), losses := [] }

theorem u13753 : Upper (D 8) (R 8) [96,12,33,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13754 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 168 145 370 338 466 338), lower := (rows 97 14 37 168 145 32 64 128 256), losses := [] }

theorem u13754 : Upper (D 8) (R 8) [96,12,33,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13755 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 168 208 307 339 403 275), lower := (rows 97 14 37 168 208 32 64 128 256), losses := [] }

theorem u13755 : Upper (D 8) (R 8) [96,12,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13756 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 168 273 242 210 210 466), lower := (rows 97 14 37 168 273 32 64 128 256), losses := [] }

theorem u13756 : Upper (D 8) (R 8) [96,12,33,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13757 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 168 274 241 209 209 465), lower := (rows 97 14 37 168 274 32 64 128 256), losses := [] }

theorem u13757 : Upper (D 8) (R 8) [96,12,33,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13758 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 168 336 179 211 147 403), lower := (rows 97 14 37 168 336 32 64 128 256), losses := [] }

theorem u13758 : Upper (D 8) (R 8) [96,12,33,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13759 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 168 400 115 83 211 339), lower := (rows 97 14 37 168 400 32 64 128 256), losses := [] }

theorem u13759 : Upper (D 8) (R 8) [96,12,33,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13760 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 200 50 433 465 401 401), lower := (rows 97 14 37 200 50 32 64 128 256), losses := [] }

theorem u13760 : Upper (D 8) (R 8) [96,12,33,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13761 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 200 145 306 370 434 306), lower := (rows 97 14 37 200 145 32 64 128 256), losses := [] }

theorem u13761 : Upper (D 8) (R 8) [96,12,33,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13762 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 200 176 307 339 403 275), lower := (rows 97 14 37 200 176 32 64 128 256), losses := [] }

theorem u13762 : Upper (D 8) (R 8) [96,12,33,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13763 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 200 273 178 242 178 434), lower := (rows 97 14 37 200 273 32 64 128 256), losses := [] }

theorem u13763 : Upper (D 8) (R 8) [96,12,33,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13764 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 200 274 177 241 177 433), lower := (rows 97 14 37 200 274 32 64 128 256), losses := [] }

theorem u13764 : Upper (D 8) (R 8) [96,12,33,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13765 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 200 304 179 211 147 403), lower := (rows 97 14 37 200 304 32 64 128 256), losses := [] }

theorem u13765 : Upper (D 8) (R 8) [96,12,33,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13766 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 200 400 51 115 179 307), lower := (rows 97 14 37 200 400 32 64 128 256), losses := [] }

theorem u13766 : Upper (D 8) (R 8) [96,12,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13766 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13767 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 265 50 240 208 208 464), lower := (rows 97 14 37 265 50 32 64 128 256), losses := [] }

theorem u13767 : Upper (D 8) (R 8) [96,12,33,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13768 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 265 82 176 240 176 432), lower := (rows 97 14 37 265 82 32 64 128 256), losses := [] }

theorem u13768 : Upper (D 8) (R 8) [96,12,33,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13769 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 265 146 240 240 240 496), lower := (rows 97 14 37 265 146 32 64 128 256), losses := [] }

theorem u13769 : Upper (D 8) (R 8) [96,12,33,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13770 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 265 176 242 210 210 466), lower := (rows 97 14 37 265 176 32 64 128 256), losses := [] }

theorem u13770 : Upper (D 8) (R 8) [96,12,33,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13771 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 265 208 178 242 178 434), lower := (rows 97 14 37 265 208 32 64 128 256), losses := [] }

theorem u13771 : Upper (D 8) (R 8) [96,12,33,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13772 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 266 145 240 240 240 496), lower := (rows 97 14 37 266 145 32 64 128 256), losses := [] }

theorem u13772 : Upper (D 8) (R 8) [96,12,33,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13773 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 266 176 241 209 209 465), lower := (rows 97 14 37 266 176 32 64 128 256), losses := [] }

theorem u13773 : Upper (D 8) (R 8) [96,12,33,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13774 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 266 208 177 241 177 433), lower := (rows 97 14 37 266 208 32 64 128 256), losses := [] }

theorem u13774 : Upper (D 8) (R 8) [96,12,33,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13775 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 280 50 225 193 193 449), lower := (rows 97 14 37 280 50 32 64 128 256), losses := [] }

theorem u13775 : Upper (D 8) (R 8) [96,12,33,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13776 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 280 145 226 226 226 482), lower := (rows 97 14 37 280 145 32 64 128 256), losses := [] }

theorem u13776 : Upper (D 8) (R 8) [96,12,33,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13777 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 280 146 225 225 225 481), lower := (rows 97 14 37 280 146 32 64 128 256), losses := [] }

theorem u13777 : Upper (D 8) (R 8) [96,12,33,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13778 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 280 176 227 195 195 451), lower := (rows 97 14 37 280 176 32 64 128 256), losses := [] }

theorem u13778 : Upper (D 8) (R 8) [96,12,33,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13779 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 280 208 163 227 163 419), lower := (rows 97 14 37 280 208 32 64 128 256), losses := [] }

theorem u13779 : Upper (D 8) (R 8) [96,12,33,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13780 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 296 82 177 209 145 401), lower := (rows 97 14 37 296 82 32 64 128 256), losses := [] }

theorem u13780 : Upper (D 8) (R 8) [96,12,33,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13781 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 296 145 242 210 210 466), lower := (rows 97 14 37 296 145 32 64 128 256), losses := [] }

theorem u13781 : Upper (D 8) (R 8) [96,12,33,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13782 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 296 146 241 209 209 465), lower := (rows 97 14 37 296 146 32 64 128 256), losses := [] }

theorem u13782 : Upper (D 8) (R 8) [96,12,33,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13783 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 296 208 179 211 147 403), lower := (rows 97 14 37 296 208 32 64 128 256), losses := [] }

theorem u13783 : Upper (D 8) (R 8) [96,12,33,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13784 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 328 50 177 209 145 401), lower := (rows 97 14 37 328 50 32 64 128 256), losses := [] }

theorem u13784 : Upper (D 8) (R 8) [96,12,33,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13785 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 328 145 178 242 178 434), lower := (rows 97 14 37 328 145 32 64 128 256), losses := [] }

theorem u13785 : Upper (D 8) (R 8) [96,12,33,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13786 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 328 146 177 241 177 433), lower := (rows 97 14 37 328 146 32 64 128 256), losses := [] }

theorem u13786 : Upper (D 8) (R 8) [96,12,33,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13787 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 328 176 179 211 147 403), lower := (rows 97 14 37 328 176 32 64 128 256), losses := [] }

theorem u13787 : Upper (D 8) (R 8) [96,12,33,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13788 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 392 50 241 209 209 465), lower := (rows 97 14 37 392 50 32 64 128 256), losses := [] }

theorem u13788 : Upper (D 8) (R 8) [96,12,33,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13789 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 392 82 177 241 177 433), lower := (rows 97 14 37 392 82 32 64 128 256), losses := [] }

theorem u13789 : Upper (D 8) (R 8) [96,12,33,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13790 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 392 145 114 114 242 370), lower := (rows 97 14 37 392 145 32 64 128 256), losses := [] }

theorem u13790 : Upper (D 8) (R 8) [96,12,33,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13791 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 392 176 115 83 211 339), lower := (rows 97 14 37 392 176 32 64 128 256), losses := [] }

theorem u13791 : Upper (D 8) (R 8) [96,12,33,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13792 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 392 208 51 115 179 307), lower := (rows 97 14 37 392 208 32 64 128 256), losses := [] }

theorem u13792 : Upper (D 8) (R 8) [96,12,33,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13793 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 56 145 481 449 449 449), lower := (rows 97 14 38 56 145 32 64 128 256), losses := [] }

theorem u13793 : Upper (D 8) (R 8) [96,12,34,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13794 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 56 208 417 449 385 385), lower := (rows 97 14 38 56 208 32 64 128 256), losses := [] }

theorem u13794 : Upper (D 8) (R 8) [96,12,34,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13795 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 56 273 225 193 193 449), lower := (rows 97 14 38 56 273 32 64 128 256), losses := [] }

theorem u13795 : Upper (D 8) (R 8) [96,12,34,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13796 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 56 336 161 193 129 385), lower := (rows 97 14 38 56 336 32 64 128 256), losses := [] }

theorem u13796 : Upper (D 8) (R 8) [96,12,34,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13797 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 56 400 225 193 193 449), lower := (rows 97 14 38 56 400 32 64 128 256), losses := [] }

theorem u13797 : Upper (D 8) (R 8) [96,12,34,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13798 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 14 38 73 145 432 496 432 432), lower := (rows 97 14 38 73 145 32 64 128 256), losses := [] }

theorem u13798 : Upper (D 8) (R 8) [96,12,34,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13799 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 14 38 73 176 433 465 401 401), lower := (rows 97 14 38 73 176 32 64 128 256), losses := [] }

theorem u13799 : Upper (D 8) (R 8) [96,12,34,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13799
end Delivery.IrregularNine14.P08
