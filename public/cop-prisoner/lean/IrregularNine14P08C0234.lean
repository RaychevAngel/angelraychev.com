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

def b14040 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 392 145 35 99 163 291), lower := (rows 97 14 84 392 145 32 64 128 256), losses := [] }

theorem u14040 : Upper (D 8) (R 8) [96,12,80,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14041 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 392 146 33 97 161 289), lower := (rows 97 14 84 392 146 32 64 128 256), losses := [] }

theorem u14041 : Upper (D 8) (R 8) [96,12,80,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14042 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 392 176 35 99 163 291), lower := (rows 97 14 84 392 176 32 64 128 256), losses := [] }

theorem u14042 : Upper (D 8) (R 8) [96,12,80,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14043 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 50 433 465 401 401), lower := (rows 97 14 100 137 50 32 64 128 256), losses := [] }

theorem u14043 : Upper (D 8) (R 8) [96,12,96,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14044 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 176 307 339 403 275), lower := (rows 97 14 100 137 176 32 64 128 256), losses := [] }

theorem u14044 : Upper (D 8) (R 8) [96,12,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14045 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 273 178 242 178 434), lower := (rows 97 14 100 137 273 32 64 128 256), losses := [] }

theorem u14045 : Upper (D 8) (R 8) [96,12,96,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14046 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 274 177 241 177 433), lower := (rows 97 14 100 137 274 32 64 128 256), losses := [] }

theorem u14046 : Upper (D 8) (R 8) [96,12,96,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14047 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 304 179 211 147 403), lower := (rows 97 14 100 137 304 32 64 128 256), losses := [] }

theorem u14047 : Upper (D 8) (R 8) [96,12,96,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14048 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 137 400 51 115 179 307), lower := (rows 97 14 100 137 400 32 64 128 256), losses := [] }

theorem u14048 : Upper (D 8) (R 8) [96,12,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14049 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 138 273 177 241 177 433), lower := (rows 97 14 100 138 273 32 64 128 256), losses := [] }

theorem u14049 : Upper (D 8) (R 8) [96,12,96,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14050 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 138 304 177 209 145 401), lower := (rows 97 14 100 138 304 32 64 128 256), losses := [] }

theorem u14050 : Upper (D 8) (R 8) [96,12,96,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14051 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 152 50 417 449 385 385), lower := (rows 97 14 100 152 50 32 64 128 256), losses := [] }

theorem u14051 : Upper (D 8) (R 8) [96,12,96,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14052 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 152 273 163 227 163 419), lower := (rows 97 14 100 152 273 32 64 128 256), losses := [] }

theorem u14052 : Upper (D 8) (R 8) [96,12,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14053 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 152 274 161 225 161 417), lower := (rows 97 14 100 152 274 32 64 128 256), losses := [] }

theorem u14053 : Upper (D 8) (R 8) [96,12,96,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14054 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 152 304 163 195 131 387), lower := (rows 97 14 100 152 304 32 64 128 256), losses := [] }

theorem u14054 : Upper (D 8) (R 8) [96,12,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14055 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 168 145 307 339 403 275), lower := (rows 97 14 100 168 145 32 64 128 256), losses := [] }

theorem u14055 : Upper (D 8) (R 8) [96,12,96,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14056 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 168 273 179 211 147 403), lower := (rows 97 14 100 168 273 32 64 128 256), losses := [] }

theorem u14056 : Upper (D 8) (R 8) [96,12,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14057 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 168 274 177 209 145 401), lower := (rows 97 14 100 168 274 32 64 128 256), losses := [] }

theorem u14057 : Upper (D 8) (R 8) [96,12,96,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14058 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 168 400 51 83 147 275), lower := (rows 97 14 100 168 400 32 64 128 256), losses := [] }

theorem u14058 : Upper (D 8) (R 8) [96,12,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14059 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 265 50 177 209 145 401), lower := (rows 97 14 100 265 50 32 64 128 256), losses := [] }

theorem u14059 : Upper (D 8) (R 8) [96,12,96,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14060 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 265 145 178 242 178 434), lower := (rows 97 14 100 265 145 32 64 128 256), losses := [] }

theorem u14060 : Upper (D 8) (R 8) [96,12,96,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14061 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 265 146 177 241 177 433), lower := (rows 97 14 100 265 146 32 64 128 256), losses := [] }

theorem u14061 : Upper (D 8) (R 8) [96,12,96,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14062 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 265 176 179 211 147 403), lower := (rows 97 14 100 265 176 32 64 128 256), losses := [] }

theorem u14062 : Upper (D 8) (R 8) [96,12,96,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14063 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 266 145 177 241 177 433), lower := (rows 97 14 100 266 145 32 64 128 256), losses := [] }

theorem u14063 : Upper (D 8) (R 8) [96,12,96,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14064 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 266 176 177 209 145 401), lower := (rows 97 14 100 266 176 32 64 128 256), losses := [] }

theorem u14064 : Upper (D 8) (R 8) [96,12,96,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14065 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 280 50 161 193 129 385), lower := (rows 97 14 100 280 50 32 64 128 256), losses := [] }

theorem u14065 : Upper (D 8) (R 8) [96,12,96,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14066 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 280 145 163 227 163 419), lower := (rows 97 14 100 280 145 32 64 128 256), losses := [] }

theorem u14066 : Upper (D 8) (R 8) [96,12,96,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14067 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 280 146 161 225 161 417), lower := (rows 97 14 100 280 146 32 64 128 256), losses := [] }

theorem u14067 : Upper (D 8) (R 8) [96,12,96,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14068 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 280 176 163 195 131 387), lower := (rows 97 14 100 280 176 32 64 128 256), losses := [] }

theorem u14068 : Upper (D 8) (R 8) [96,12,96,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14069 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 296 145 179 211 147 403), lower := (rows 97 14 100 296 145 32 64 128 256), losses := [] }

theorem u14069 : Upper (D 8) (R 8) [96,12,96,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14070 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 296 146 177 209 145 401), lower := (rows 97 14 100 296 146 32 64 128 256), losses := [] }

theorem u14070 : Upper (D 8) (R 8) [96,12,96,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14071 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 392 50 177 209 145 401), lower := (rows 97 14 100 392 50 32 64 128 256), losses := [] }

theorem u14071 : Upper (D 8) (R 8) [96,12,96,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14072 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 392 145 51 115 179 307), lower := (rows 97 14 100 392 145 32 64 128 256), losses := [] }

theorem u14072 : Upper (D 8) (R 8) [96,12,96,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14073 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 100 392 176 51 83 147 275), lower := (rows 97 14 100 392 176 32 64 128 256), losses := [] }

theorem u14073 : Upper (D 8) (R 8) [96,12,96,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14074 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 50 368 368 496 368), lower := (rows 97 14 133 137 50 32 64 128 256), losses := [] }

theorem u14074 : Upper (D 8) (R 8) [96,12,129,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14075 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 82 304 368 432 304), lower := (rows 97 14 133 137 82 32 64 128 256), losses := [] }

theorem u14075 : Upper (D 8) (R 8) [96,12,129,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14076 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 274 112 112 240 368), lower := (rows 97 14 133 137 274 32 64 128 256), losses := [] }

theorem u14076 : Upper (D 8) (R 8) [96,12,129,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14077 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 304 114 114 242 370), lower := (rows 97 14 133 137 304 32 64 128 256), losses := [] }

theorem u14077 : Upper (D 8) (R 8) [96,12,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14078 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 97 14 133 137 336 50 114 178 306), lower := (rows 97 14 133 137 336 32 64 128 256), losses := [] }

theorem u14078 : Upper (D 8) (R 8) [96,12,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14079 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 133 138 273 112 112 240 368), lower := (rows 97 14 133 138 273 32 64 128 256), losses := [] }

theorem u14079 : Upper (D 8) (R 8) [96,12,129,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14080 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 133 138 304 113 113 241 369), lower := (rows 97 14 133 138 304 32 64 128 256), losses := [] }

theorem u14080 : Upper (D 8) (R 8) [96,12,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14081 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 133 138 336 49 113 177 305), lower := (rows 97 14 133 138 336 32 64 128 256), losses := [] }

theorem u14081 : Upper (D 8) (R 8) [96,12,129,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14082 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 50 353 353 481 353), lower := (rows 97 14 133 152 50 32 64 128 256), losses := [] }

theorem u14082 : Upper (D 8) (R 8) [96,12,129,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14083 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 82 289 353 417 289), lower := (rows 97 14 133 152 82 32 64 128 256), losses := [] }

theorem u14083 : Upper (D 8) (R 8) [96,12,129,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14084 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 273 98 98 226 354), lower := (rows 97 14 133 152 273 32 64 128 256), losses := [] }

theorem u14084 : Upper (D 8) (R 8) [96,12,129,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14085 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 274 97 97 225 353), lower := (rows 97 14 133 152 274 32 64 128 256), losses := [] }

theorem u14085 : Upper (D 8) (R 8) [96,12,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14086 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 304 99 99 227 355), lower := (rows 97 14 133 152 304 32 64 128 256), losses := [] }

theorem u14086 : Upper (D 8) (R 8) [96,12,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14087 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 152 336 35 99 163 291), lower := (rows 97 14 133 152 336 32 64 128 256), losses := [] }

theorem u14087 : Upper (D 8) (R 8) [96,12,129,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14088 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 50 369 337 465 337), lower := (rows 97 14 133 168 50 32 64 128 256), losses := [] }

theorem u14088 : Upper (D 8) (R 8) [96,12,129,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14089 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 82 305 369 433 305), lower := (rows 97 14 133 168 82 32 64 128 256), losses := [] }

theorem u14089 : Upper (D 8) (R 8) [96,12,129,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14090 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 273 114 114 242 370), lower := (rows 97 14 133 168 273 32 64 128 256), losses := [] }

theorem u14090 : Upper (D 8) (R 8) [96,12,129,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14091 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 274 113 113 241 369), lower := (rows 97 14 133 168 274 32 64 128 256), losses := [] }

theorem u14091 : Upper (D 8) (R 8) [96,12,129,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14092 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 304 115 83 211 339), lower := (rows 97 14 133 168 304 32 64 128 256), losses := [] }

theorem u14092 : Upper (D 8) (R 8) [96,12,129,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14093 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 168 336 51 115 179 307), lower := (rows 97 14 133 168 336 32 64 128 256), losses := [] }

theorem u14093 : Upper (D 8) (R 8) [96,12,129,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14094 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 200 50 305 369 433 305), lower := (rows 97 14 133 200 50 32 64 128 256), losses := [] }

theorem u14094 : Upper (D 8) (R 8) [96,12,129,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14095 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 200 273 50 114 178 306), lower := (rows 97 14 133 200 273 32 64 128 256), losses := [] }

theorem u14095 : Upper (D 8) (R 8) [96,12,129,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14096 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 200 274 49 113 177 305), lower := (rows 97 14 133 200 274 32 64 128 256), losses := [] }

theorem u14096 : Upper (D 8) (R 8) [96,12,129,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14097 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 200 304 51 115 179 307), lower := (rows 97 14 133 200 304 32 64 128 256), losses := [] }

theorem u14097 : Upper (D 8) (R 8) [96,12,129,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14098 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 265 50 240 240 240 496), lower := (rows 97 14 133 265 50 32 64 128 256), losses := [] }

theorem u14098 : Upper (D 8) (R 8) [96,12,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14099 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 265 82 176 240 176 432), lower := (rows 97 14 133 265 82 32 64 128 256), losses := [] }

theorem u14099 : Upper (D 8) (R 8) [96,12,129,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14099
end Delivery.IrregularNine14.P08
