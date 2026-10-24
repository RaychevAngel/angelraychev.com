import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4020 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 137 304 248 216 216 472), lower := (rows 97 7 7 137 304 32 64 128 256), losses := [] }

theorem u4020 : Upper (D 3) (R 3) [96,5,3,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4020
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4021 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 137 400 120 120 248 376), lower := (rows 97 7 7 137 400 32 64 128 256), losses := [] }

theorem u4021 : Upper (D 3) (R 3) [96,5,3,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4021
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4022 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 152 273 232 232 232 488), lower := (rows 97 7 7 152 273 32 64 128 256), losses := [] }

theorem u4022 : Upper (D 3) (R 3) [96,5,3,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4022
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4023 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 152 280 225 225 225 481), lower := (rows 97 7 7 152 280 32 64 128 256), losses := [] }

theorem u4023 : Upper (D 3) (R 3) [96,5,3,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4023
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4024 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 152 304 233 201 201 457), lower := (rows 97 7 7 152 304 32 64 128 256), losses := [] }

theorem u4024 : Upper (D 3) (R 3) [96,5,3,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4024
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4025 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 208 313 345 409 281), lower := (rows 97 7 7 168 208 32 64 128 256), losses := [] }

theorem u4025 : Upper (D 3) (R 3) [96,5,3,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4025
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4026 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 273 248 216 216 472), lower := (rows 97 7 7 168 273 32 64 128 256), losses := [] }

theorem u4026 : Upper (D 3) (R 3) [96,5,3,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4026
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4027 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 280 241 209 209 465), lower := (rows 97 7 7 168 280 32 64 128 256), losses := [] }

theorem u4027 : Upper (D 3) (R 3) [96,5,3,160,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4027
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4028 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 336 185 217 153 409), lower := (rows 97 7 7 168 336 32 64 128 256), losses := [] }

theorem u4028 : Upper (D 3) (R 3) [96,5,3,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4028
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4029 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 400 121 89 217 345), lower := (rows 97 7 7 168 400 32 64 128 256), losses := [] }

theorem u4029 : Upper (D 3) (R 3) [96,5,3,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4029
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4030 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 25 146 480 480 480 480), lower := (rows 97 7 13 25 146 32 64 128 256), losses := [] }

theorem u4030 : Upper (D 3) (R 3) [96,5,9,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4030
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4031 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 25 274 224 224 224 480), lower := (rows 97 7 13 25 274 32 64 128 256), losses := [] }

theorem u4031 : Upper (D 3) (R 3) [96,5,9,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4031
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4032 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 25 400 226 226 226 482), lower := (rows 97 7 13 25 400 32 64 128 256), losses := [] }

theorem u4032 : Upper (D 3) (R 3) [96,5,9,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4032
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4033 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 26 145 480 480 480 480), lower := (rows 97 7 13 26 145 32 64 128 256), losses := [] }

theorem u4033 : Upper (D 3) (R 3) [96,5,9,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4033
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4034 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 26 176 481 449 449 449), lower := (rows 97 7 13 26 176 32 64 128 256), losses := [] }

theorem u4034 : Upper (D 3) (R 3) [96,5,9,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4034
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4035 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 26 273 224 224 224 480), lower := (rows 97 7 13 26 273 32 64 128 256), losses := [] }

theorem u4035 : Upper (D 3) (R 3) [96,5,9,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4035
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4036 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 26 304 225 193 193 449), lower := (rows 97 7 13 26 304 32 64 128 256), losses := [] }

theorem u4036 : Upper (D 3) (R 3) [96,5,9,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4036
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4037 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 26 400 225 225 225 481), lower := (rows 97 7 13 26 400 32 64 128 256), losses := [] }

theorem u4037 : Upper (D 3) (R 3) [96,5,9,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4037
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4038 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 145 496 464 464 464), lower := (rows 97 7 13 42 145 32 64 128 256), losses := [] }

theorem u4038 : Upper (D 3) (R 3) [96,5,9,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4038
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4039 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 208 433 465 401 401), lower := (rows 97 7 13 42 208 32 64 128 256), losses := [] }

theorem u4039 : Upper (D 3) (R 3) [96,5,9,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4039
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4040 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 273 240 208 208 464), lower := (rows 97 7 13 42 273 32 64 128 256), losses := [] }

theorem u4040 : Upper (D 3) (R 3) [96,5,9,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4040
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4041 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 336 177 209 145 401), lower := (rows 97 7 13 42 336 32 64 128 256), losses := [] }

theorem u4041 : Upper (D 3) (R 3) [96,5,9,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4041
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4042 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 400 241 209 209 465), lower := (rows 97 7 13 42 400 32 64 128 256), losses := [] }

theorem u4042 : Upper (D 3) (R 3) [96,5,9,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4042
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4043 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 13 56 82 417 449 385 385), lower := (rows 97 7 13 56 82 32 64 128 256), losses := [] }

theorem u4043 : Upper (D 3) (R 3) [96,5,9,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4043
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4044 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 145 482 450 450 450), lower := (rows 97 7 13 56 145 32 64 128 256), losses := [] }

theorem u4044 : Upper (D 3) (R 3) [96,5,9,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4044
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4045 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 146 481 449 449 449), lower := (rows 97 7 13 56 146 32 64 128 256), losses := [] }

theorem u4045 : Upper (D 3) (R 3) [96,5,9,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4045
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4046 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 208 419 451 387 387), lower := (rows 97 7 13 56 208 32 64 128 256), losses := [] }

theorem u4046 : Upper (D 3) (R 3) [96,5,9,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4046
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4047 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 273 226 194 194 450), lower := (rows 97 7 13 56 273 32 64 128 256), losses := [] }

theorem u4047 : Upper (D 3) (R 3) [96,5,9,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4047
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4048 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 274 225 193 193 449), lower := (rows 97 7 13 56 274 32 64 128 256), losses := [] }

theorem u4048 : Upper (D 3) (R 3) [96,5,9,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4048
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4049 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 336 163 195 131 387), lower := (rows 97 7 13 56 336 32 64 128 256), losses := [] }

theorem u4049 : Upper (D 3) (R 3) [96,5,9,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4049
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4050 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 400 227 195 195 451), lower := (rows 97 7 13 56 400 32 64 128 256), losses := [] }

theorem u4050 : Upper (D 3) (R 3) [96,5,9,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4050
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4051 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 137 50 496 464 464 464), lower := (rows 97 7 13 137 50 32 64 128 256), losses := [] }

theorem u4051 : Upper (D 3) (R 3) [96,5,9,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4051
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4052 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 137 146 368 368 496 368), lower := (rows 97 7 13 137 146 32 64 128 256), losses := [] }

theorem u4052 : Upper (D 3) (R 3) [96,5,9,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4052
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4053 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 137 176 370 338 466 338), lower := (rows 97 7 13 137 176 32 64 128 256), losses := [] }

theorem u4053 : Upper (D 3) (R 3) [96,5,9,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4053
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4054 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 137 274 240 240 240 496), lower := (rows 97 7 13 137 274 32 64 128 256), losses := [] }

theorem u4054 : Upper (D 3) (R 3) [96,5,9,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4054
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4055 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 137 304 242 210 210 466), lower := (rows 97 7 13 137 304 32 64 128 256), losses := [] }

theorem u4055 : Upper (D 3) (R 3) [96,5,9,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4055
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4056 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 137 400 114 114 242 370), lower := (rows 97 7 13 137 400 32 64 128 256), losses := [] }

theorem u4056 : Upper (D 3) (R 3) [96,5,9,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4056
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4057 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 145 368 368 496 368), lower := (rows 97 7 13 138 145 32 64 128 256), losses := [] }

theorem u4057 : Upper (D 3) (R 3) [96,5,9,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4057
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4058 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 176 369 337 465 337), lower := (rows 97 7 13 138 176 32 64 128 256), losses := [] }

theorem u4058 : Upper (D 3) (R 3) [96,5,9,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4058
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4059 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 273 240 240 240 496), lower := (rows 97 7 13 138 273 32 64 128 256), losses := [] }

theorem u4059 : Upper (D 3) (R 3) [96,5,9,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4059
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4060 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 304 241 209 209 465), lower := (rows 97 7 13 138 304 32 64 128 256), losses := [] }

theorem u4060 : Upper (D 3) (R 3) [96,5,9,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4060
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4061 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 400 113 113 241 369), lower := (rows 97 7 13 138 400 32 64 128 256), losses := [] }

theorem u4061 : Upper (D 3) (R 3) [96,5,9,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4061
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4062 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 152 50 481 449 449 449), lower := (rows 97 7 13 152 50 32 64 128 256), losses := [] }

theorem u4062 : Upper (D 3) (R 3) [96,5,9,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4062
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4063 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 152 273 226 226 226 482), lower := (rows 97 7 13 152 273 32 64 128 256), losses := [] }

theorem u4063 : Upper (D 3) (R 3) [96,5,9,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4063
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4064 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 152 274 225 225 225 481), lower := (rows 97 7 13 152 274 32 64 128 256), losses := [] }

theorem u4064 : Upper (D 3) (R 3) [96,5,9,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4064
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4065 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 152 304 227 195 195 451), lower := (rows 97 7 13 152 304 32 64 128 256), losses := [] }

theorem u4065 : Upper (D 3) (R 3) [96,5,9,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4065
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4066 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 82 433 465 401 401), lower := (rows 97 7 13 168 82 32 64 128 256), losses := [] }

theorem u4066 : Upper (D 3) (R 3) [96,5,9,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4066
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4067 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 145 370 338 466 338), lower := (rows 97 7 13 168 145 32 64 128 256), losses := [] }

theorem u4067 : Upper (D 3) (R 3) [96,5,9,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4067
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4068 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 146 369 337 465 337), lower := (rows 97 7 13 168 146 32 64 128 256), losses := [] }

theorem u4068 : Upper (D 3) (R 3) [96,5,9,160,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4068
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4069 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 208 307 339 403 275), lower := (rows 97 7 13 168 208 32 64 128 256), losses := [] }

theorem u4069 : Upper (D 3) (R 3) [96,5,9,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4069
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4070 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 273 242 210 210 466), lower := (rows 97 7 13 168 273 32 64 128 256), losses := [] }

theorem u4070 : Upper (D 3) (R 3) [96,5,9,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4070
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4071 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 274 241 209 209 465), lower := (rows 97 7 13 168 274 32 64 128 256), losses := [] }

theorem u4071 : Upper (D 3) (R 3) [96,5,9,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4071
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4072 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 336 179 211 147 403), lower := (rows 97 7 13 168 336 32 64 128 256), losses := [] }

theorem u4072 : Upper (D 3) (R 3) [96,5,9,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4072
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4073 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 400 115 83 211 339), lower := (rows 97 7 13 168 400 32 64 128 256), losses := [] }

theorem u4073 : Upper (D 3) (R 3) [96,5,9,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4073
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4074 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 265 50 240 208 208 464), lower := (rows 97 7 13 265 50 32 64 128 256), losses := [] }

theorem u4074 : Upper (D 3) (R 3) [96,5,9,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4074
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4075 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 265 146 240 240 240 496), lower := (rows 97 7 13 265 146 32 64 128 256), losses := [] }

theorem u4075 : Upper (D 3) (R 3) [96,5,9,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4075
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4076 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 265 176 242 210 210 466), lower := (rows 97 7 13 265 176 32 64 128 256), losses := [] }

theorem u4076 : Upper (D 3) (R 3) [96,5,9,257,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4076
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4077 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 266 145 240 240 240 496), lower := (rows 97 7 13 266 145 32 64 128 256), losses := [] }

theorem u4077 : Upper (D 3) (R 3) [96,5,9,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4077
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4078 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 266 176 241 209 209 465), lower := (rows 97 7 13 266 176 32 64 128 256), losses := [] }

theorem u4078 : Upper (D 3) (R 3) [96,5,9,258,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4078
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4079 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 280 50 225 193 193 449), lower := (rows 97 7 13 280 50 32 64 128 256), losses := [] }

theorem u4079 : Upper (D 3) (R 3) [96,5,9,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4079
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4079
end Delivery.IrregularNine14.P03
