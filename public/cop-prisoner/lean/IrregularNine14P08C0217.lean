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

def b13020 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 137 304 178 242 178 434), lower := (rows 97 7 76 137 304 32 64 128 256), losses := [] }

theorem u13020 : Upper (D 8) (R 8) [96,5,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13021 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 137 400 50 114 178 306), lower := (rows 97 7 76 137 400 32 64 128 256), losses := [] }

theorem u13021 : Upper (D 8) (R 8) [96,5,72,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13022 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 138 145 304 368 432 304), lower := (rows 97 7 76 138 145 32 64 128 256), losses := [] }

theorem u13022 : Upper (D 8) (R 8) [96,5,72,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13023 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 138 176 305 369 433 305), lower := (rows 97 7 76 138 176 32 64 128 256), losses := [] }

theorem u13023 : Upper (D 8) (R 8) [96,5,72,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13024 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 138 273 176 240 176 432), lower := (rows 97 7 76 138 273 32 64 128 256), losses := [] }

theorem u13024 : Upper (D 8) (R 8) [96,5,72,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13025 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 138 304 177 241 177 433), lower := (rows 97 7 76 138 304 32 64 128 256), losses := [] }

theorem u13025 : Upper (D 8) (R 8) [96,5,72,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13026 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 138 400 49 113 177 305), lower := (rows 97 7 76 138 400 32 64 128 256), losses := [] }

theorem u13026 : Upper (D 8) (R 8) [96,5,72,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13027 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 152 50 417 481 417 417), lower := (rows 97 7 76 152 50 32 64 128 256), losses := [] }

theorem u13027 : Upper (D 8) (R 8) [96,5,72,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13028 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 152 273 162 226 162 418), lower := (rows 97 7 76 152 273 32 64 128 256), losses := [] }

theorem u13028 : Upper (D 8) (R 8) [96,5,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13029 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 152 274 161 225 161 417), lower := (rows 97 7 76 152 274 32 64 128 256), losses := [] }

theorem u13029 : Upper (D 8) (R 8) [96,5,72,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13030 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 152 304 163 227 163 419), lower := (rows 97 7 76 152 304 32 64 128 256), losses := [] }

theorem u13030 : Upper (D 8) (R 8) [96,5,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13031 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 168 50 433 465 401 401), lower := (rows 97 7 76 168 50 32 64 128 256), losses := [] }

theorem u13031 : Upper (D 8) (R 8) [96,5,72,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13032 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 168 145 306 370 434 306), lower := (rows 97 7 76 168 145 32 64 128 256), losses := [] }

theorem u13032 : Upper (D 8) (R 8) [96,5,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13033 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 168 146 305 369 433 305), lower := (rows 97 7 76 168 146 32 64 128 256), losses := [] }

theorem u13033 : Upper (D 8) (R 8) [96,5,72,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13034 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 168 273 178 242 178 434), lower := (rows 97 7 76 168 273 32 64 128 256), losses := [] }

theorem u13034 : Upper (D 8) (R 8) [96,5,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13035 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 168 274 177 241 177 433), lower := (rows 97 7 76 168 274 32 64 128 256), losses := [] }

theorem u13035 : Upper (D 8) (R 8) [96,5,72,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13036 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 168 304 179 211 147 403), lower := (rows 97 7 76 168 304 32 64 128 256), losses := [] }

theorem u13036 : Upper (D 8) (R 8) [96,5,72,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13037 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 168 400 51 115 179 307), lower := (rows 97 7 76 168 400 32 64 128 256), losses := [] }

theorem u13037 : Upper (D 8) (R 8) [96,5,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13038 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 265 50 176 240 176 432), lower := (rows 97 7 76 265 50 32 64 128 256), losses := [] }

theorem u13038 : Upper (D 8) (R 8) [96,5,72,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13039 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 265 146 176 240 176 432), lower := (rows 97 7 76 265 146 32 64 128 256), losses := [] }

theorem u13039 : Upper (D 8) (R 8) [96,5,72,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13040 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 265 176 178 242 178 434), lower := (rows 97 7 76 265 176 32 64 128 256), losses := [] }

theorem u13040 : Upper (D 8) (R 8) [96,5,72,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13041 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 266 145 176 240 176 432), lower := (rows 97 7 76 266 145 32 64 128 256), losses := [] }

theorem u13041 : Upper (D 8) (R 8) [96,5,72,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13042 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 266 176 177 241 177 433), lower := (rows 97 7 76 266 176 32 64 128 256), losses := [] }

theorem u13042 : Upper (D 8) (R 8) [96,5,72,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13043 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 280 50 161 225 161 417), lower := (rows 97 7 76 280 50 32 64 128 256), losses := [] }

theorem u13043 : Upper (D 8) (R 8) [96,5,72,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13044 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 280 145 162 226 162 418), lower := (rows 97 7 76 280 145 32 64 128 256), losses := [] }

theorem u13044 : Upper (D 8) (R 8) [96,5,72,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13045 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 280 146 161 225 161 417), lower := (rows 97 7 76 280 146 32 64 128 256), losses := [] }

theorem u13045 : Upper (D 8) (R 8) [96,5,72,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13046 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 280 176 163 227 163 419), lower := (rows 97 7 76 280 176 32 64 128 256), losses := [] }

theorem u13046 : Upper (D 8) (R 8) [96,5,72,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13047 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 296 50 177 209 145 401), lower := (rows 97 7 76 296 50 32 64 128 256), losses := [] }

theorem u13047 : Upper (D 8) (R 8) [96,5,72,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13048 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 296 145 178 242 178 434), lower := (rows 97 7 76 296 145 32 64 128 256), losses := [] }

theorem u13048 : Upper (D 8) (R 8) [96,5,72,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13049 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 296 146 177 241 177 433), lower := (rows 97 7 76 296 146 32 64 128 256), losses := [] }

theorem u13049 : Upper (D 8) (R 8) [96,5,72,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13050 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 296 176 179 211 147 403), lower := (rows 97 7 76 296 176 32 64 128 256), losses := [] }

theorem u13050 : Upper (D 8) (R 8) [96,5,72,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13051 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 392 50 177 241 177 433), lower := (rows 97 7 76 392 50 32 64 128 256), losses := [] }

theorem u13051 : Upper (D 8) (R 8) [96,5,72,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13052 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 392 145 50 114 178 306), lower := (rows 97 7 76 392 145 32 64 128 256), losses := [] }

theorem u13052 : Upper (D 8) (R 8) [96,5,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13053 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 392 146 49 113 177 305), lower := (rows 97 7 76 392 146 32 64 128 256), losses := [] }

theorem u13053 : Upper (D 8) (R 8) [96,5,72,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13054 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 76 392 176 51 115 179 307), lower := (rows 97 7 76 392 176 32 64 128 256), losses := [] }

theorem u13054 : Upper (D 8) (R 8) [96,5,72,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13055 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 25 176 426 458 394 394), lower := (rows 97 7 100 25 176 32 64 128 256), losses := [] }

theorem u13055 : Upper (D 8) (R 8) [96,5,96,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13056 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 25 304 170 202 138 394), lower := (rows 97 7 100 25 304 32 64 128 256), losses := [] }

theorem u13056 : Upper (D 8) (R 8) [96,5,96,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13057 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 25 400 170 234 170 426), lower := (rows 97 7 100 25 400 32 64 128 256), losses := [] }

theorem u13057 : Upper (D 8) (R 8) [96,5,96,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13058 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 56 417 449 385 385), lower := (rows 97 7 100 26 56 32 64 128 256), losses := [] }

theorem u13058 : Upper (D 8) (R 8) [96,5,96,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13059 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 152 417 481 417 417), lower := (rows 97 7 100 26 152 32 64 128 256), losses := [] }

theorem u13059 : Upper (D 8) (R 8) [96,5,96,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13060 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 176 425 457 393 393), lower := (rows 97 7 100 26 176 32 64 128 256), losses := [] }

theorem u13060 : Upper (D 8) (R 8) [96,5,96,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13061 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 280 161 225 161 417), lower := (rows 97 7 100 26 280 32 64 128 256), losses := [] }

theorem u13061 : Upper (D 8) (R 8) [96,5,96,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13062 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 304 169 201 137 393), lower := (rows 97 7 100 26 304 32 64 128 256), losses := [] }

theorem u13062 : Upper (D 8) (R 8) [96,5,96,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13063 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 400 169 233 169 425), lower := (rows 97 7 100 26 400 32 64 128 256), losses := [] }

theorem u13063 : Upper (D 8) (R 8) [96,5,96,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13064 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 42 145 440 472 408 408), lower := (rows 97 7 100 42 145 32 64 128 256), losses := [] }

theorem u13064 : Upper (D 8) (R 8) [96,5,96,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13065 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 42 152 433 465 401 401), lower := (rows 97 7 100 42 152 32 64 128 256), losses := [] }

theorem u13065 : Upper (D 8) (R 8) [96,5,96,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13066 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 42 273 184 216 152 408), lower := (rows 97 7 100 42 273 32 64 128 256), losses := [] }

theorem u13066 : Upper (D 8) (R 8) [96,5,96,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13067 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 42 280 177 209 145 401), lower := (rows 97 7 100 42 280 32 64 128 256), losses := [] }

theorem u13067 : Upper (D 8) (R 8) [96,5,96,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13068 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 42 400 185 217 153 409), lower := (rows 97 7 100 42 400 32 64 128 256), losses := [] }

theorem u13068 : Upper (D 8) (R 8) [96,5,96,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13069 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 56 145 426 458 394 394), lower := (rows 97 7 100 56 145 32 64 128 256), losses := [] }

theorem u13069 : Upper (D 8) (R 8) [96,5,96,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13070 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 56 146 425 457 393 393), lower := (rows 97 7 100 56 146 32 64 128 256), losses := [] }

theorem u13070 : Upper (D 8) (R 8) [96,5,96,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13071 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 56 152 419 451 387 387), lower := (rows 97 7 100 56 152 32 64 128 256), losses := [] }

theorem u13071 : Upper (D 8) (R 8) [96,5,96,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13072 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 56 273 170 202 138 394), lower := (rows 97 7 100 56 273 32 64 128 256), losses := [] }

theorem u13072 : Upper (D 8) (R 8) [96,5,96,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13073 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 56 274 169 201 137 393), lower := (rows 97 7 100 56 274 32 64 128 256), losses := [] }

theorem u13073 : Upper (D 8) (R 8) [96,5,96,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13074 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 56 280 163 195 131 387), lower := (rows 97 7 100 56 280 32 64 128 256), losses := [] }

theorem u13074 : Upper (D 8) (R 8) [96,5,96,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13075 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 56 400 171 203 139 395), lower := (rows 97 7 100 56 400 32 64 128 256), losses := [] }

theorem u13075 : Upper (D 8) (R 8) [96,5,96,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13076 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 146 312 376 440 312), lower := (rows 97 7 100 137 146 32 64 128 256), losses := [] }

theorem u13076 : Upper (D 8) (R 8) [96,5,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13077 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 176 314 346 410 282), lower := (rows 97 7 100 137 176 32 64 128 256), losses := [] }

theorem u13077 : Upper (D 8) (R 8) [96,5,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13078 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 274 184 248 184 440), lower := (rows 97 7 100 137 274 32 64 128 256), losses := [] }

theorem u13078 : Upper (D 8) (R 8) [96,5,96,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13079 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 280 178 242 178 434), lower := (rows 97 7 100 137 280 32 64 128 256), losses := [] }

theorem u13079 : Upper (D 8) (R 8) [96,5,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13079
end Delivery.IrregularNine14.P08
