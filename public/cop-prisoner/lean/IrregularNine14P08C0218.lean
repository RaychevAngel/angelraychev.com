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

def b13080 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 304 186 218 154 410), lower := (rows 97 7 100 137 304 32 64 128 256), losses := [] }

theorem u13080 : Upper (D 8) (R 8) [96,5,96,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13081 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 400 58 122 186 314), lower := (rows 97 7 100 137 400 32 64 128 256), losses := [] }

theorem u13081 : Upper (D 8) (R 8) [96,5,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13082 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 176 313 345 409 281), lower := (rows 97 7 100 138 176 32 64 128 256), losses := [] }

theorem u13082 : Upper (D 8) (R 8) [96,5,96,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13083 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 273 184 248 184 440), lower := (rows 97 7 100 138 273 32 64 128 256), losses := [] }

theorem u13083 : Upper (D 8) (R 8) [96,5,96,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13084 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 280 177 241 177 433), lower := (rows 97 7 100 138 280 32 64 128 256), losses := [] }

theorem u13084 : Upper (D 8) (R 8) [96,5,96,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13085 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 304 185 217 153 409), lower := (rows 97 7 100 138 304 32 64 128 256), losses := [] }

theorem u13085 : Upper (D 8) (R 8) [96,5,96,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13086 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 400 57 121 185 313), lower := (rows 97 7 100 138 400 32 64 128 256), losses := [] }

theorem u13086 : Upper (D 8) (R 8) [96,5,96,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13087 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 152 273 170 234 170 426), lower := (rows 97 7 100 152 273 32 64 128 256), losses := [] }

theorem u13087 : Upper (D 8) (R 8) [96,5,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13088 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 152 274 169 233 169 425), lower := (rows 97 7 100 152 274 32 64 128 256), losses := [] }

theorem u13088 : Upper (D 8) (R 8) [96,5,96,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13089 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 152 280 163 227 163 419), lower := (rows 97 7 100 152 280 32 64 128 256), losses := [] }

theorem u13089 : Upper (D 8) (R 8) [96,5,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13090 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 152 304 171 203 139 395), lower := (rows 97 7 100 152 304 32 64 128 256), losses := [] }

theorem u13090 : Upper (D 8) (R 8) [96,5,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13091 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 168 273 186 218 154 410), lower := (rows 97 7 100 168 273 32 64 128 256), losses := [] }

theorem u13091 : Upper (D 8) (R 8) [96,5,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13092 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 168 274 185 217 153 409), lower := (rows 97 7 100 168 274 32 64 128 256), losses := [] }

theorem u13092 : Upper (D 8) (R 8) [96,5,96,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13093 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 168 280 179 211 147 403), lower := (rows 97 7 100 168 280 32 64 128 256), losses := [] }

theorem u13093 : Upper (D 8) (R 8) [96,5,96,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13094 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 168 400 59 91 155 283), lower := (rows 97 7 100 168 400 32 64 128 256), losses := [] }

theorem u13094 : Upper (D 8) (R 8) [96,5,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13095 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 56 480 480 480 480), lower := (rows 97 7 133 26 56 32 64 128 256), losses := [] }

theorem u13095 : Upper (D 8) (R 8) [96,5,129,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13096 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 152 352 352 480 352), lower := (rows 97 7 133 26 152 32 64 128 256), losses := [] }

theorem u13096 : Upper (D 8) (R 8) [96,5,129,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13097 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 176 360 360 488 360), lower := (rows 97 7 133 26 176 32 64 128 256), losses := [] }

theorem u13097 : Upper (D 8) (R 8) [96,5,129,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13098 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 208 296 360 424 296), lower := (rows 97 7 133 26 208 32 64 128 256), losses := [] }

theorem u13098 : Upper (D 8) (R 8) [96,5,129,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13099 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 280 224 224 224 480), lower := (rows 97 7 133 26 280 32 64 128 256), losses := [] }

theorem u13099 : Upper (D 8) (R 8) [96,5,129,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13100 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 304 232 232 232 488), lower := (rows 97 7 133 26 304 32 64 128 256), losses := [] }

theorem u13100 : Upper (D 8) (R 8) [96,5,129,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13101 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 336 168 232 168 424), lower := (rows 97 7 133 26 336 32 64 128 256), losses := [] }

theorem u13101 : Upper (D 8) (R 8) [96,5,129,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13102 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 400 104 104 232 360), lower := (rows 97 7 133 26 400 32 64 128 256), losses := [] }

theorem u13102 : Upper (D 8) (R 8) [96,5,129,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13103 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 88 432 496 432 432), lower := (rows 97 7 133 42 88 32 64 128 256), losses := [] }

theorem u13103 : Upper (D 8) (R 8) [96,5,129,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13104 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 152 368 368 496 368), lower := (rows 97 7 133 42 152 32 64 128 256), losses := [] }

theorem u13104 : Upper (D 8) (R 8) [96,5,129,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13105 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 176 376 344 472 344), lower := (rows 97 7 133 42 176 32 64 128 256), losses := [] }

theorem u13105 : Upper (D 8) (R 8) [96,5,129,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13106 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 208 312 376 440 312), lower := (rows 97 7 133 42 208 32 64 128 256), losses := [] }

theorem u13106 : Upper (D 8) (R 8) [96,5,129,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13107 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 280 240 240 240 496), lower := (rows 97 7 133 42 280 32 64 128 256), losses := [] }

theorem u13107 : Upper (D 8) (R 8) [96,5,129,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13108 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 304 248 216 216 472), lower := (rows 97 7 133 42 304 32 64 128 256), losses := [] }

theorem u13108 : Upper (D 8) (R 8) [96,5,129,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13109 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 336 184 248 184 440), lower := (rows 97 7 133 42 336 32 64 128 256), losses := [] }

theorem u13109 : Upper (D 8) (R 8) [96,5,129,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13110 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 400 120 120 248 376), lower := (rows 97 7 133 42 400 32 64 128 256), losses := [] }

theorem u13110 : Upper (D 8) (R 8) [96,5,129,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13111 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 82 424 488 424 424), lower := (rows 97 7 133 56 82 32 64 128 256), losses := [] }

theorem u13111 : Upper (D 8) (R 8) [96,5,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13112 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 146 360 360 488 360), lower := (rows 97 7 133 56 146 32 64 128 256), losses := [] }

theorem u13112 : Upper (D 8) (R 8) [96,5,129,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13113 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 133 56 152 354 354 482 354), lower := (rows 97 7 133 56 152 32 64 128 256), losses := [] }

theorem u13113 : Upper (D 8) (R 8) [96,5,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13114 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 208 298 362 426 298), lower := (rows 97 7 133 56 208 32 64 128 256), losses := [] }

theorem u13114 : Upper (D 8) (R 8) [96,5,129,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13115 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 274 232 232 232 488), lower := (rows 97 7 133 56 274 32 64 128 256), losses := [] }

theorem u13115 : Upper (D 8) (R 8) [96,5,129,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13116 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 280 226 226 226 482), lower := (rows 97 7 133 56 280 32 64 128 256), losses := [] }

theorem u13116 : Upper (D 8) (R 8) [96,5,129,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13117 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 336 170 234 170 426), lower := (rows 97 7 133 56 336 32 64 128 256), losses := [] }

theorem u13117 : Upper (D 8) (R 8) [96,5,129,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13118 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 400 106 106 234 362), lower := (rows 97 7 133 56 400 32 64 128 256), losses := [] }

theorem u13118 : Upper (D 8) (R 8) [96,5,129,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13119 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 74 152 304 368 432 304), lower := (rows 97 7 133 74 152 32 64 128 256), losses := [] }

theorem u13119 : Upper (D 8) (R 8) [96,5,129,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13120 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 74 176 312 376 440 312), lower := (rows 97 7 133 74 176 32 64 128 256), losses := [] }

theorem u13120 : Upper (D 8) (R 8) [96,5,129,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13121 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 74 280 176 240 176 432), lower := (rows 97 7 133 74 280 32 64 128 256), losses := [] }

theorem u13121 : Upper (D 8) (R 8) [96,5,129,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13122 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 74 304 184 248 184 440), lower := (rows 97 7 133 74 304 32 64 128 256), losses := [] }

theorem u13122 : Upper (D 8) (R 8) [96,5,129,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13123 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 74 400 56 120 184 312), lower := (rows 97 7 133 74 400 32 64 128 256), losses := [] }

theorem u13123 : Upper (D 8) (R 8) [96,5,129,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13124 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 88 146 296 360 424 296), lower := (rows 97 7 133 88 146 32 64 128 256), losses := [] }

theorem u13124 : Upper (D 8) (R 8) [96,5,129,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13125 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 88 176 298 362 426 298), lower := (rows 97 7 133 88 176 32 64 128 256), losses := [] }

theorem u13125 : Upper (D 8) (R 8) [96,5,129,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13126 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 88 274 168 232 168 424), lower := (rows 97 7 133 88 274 32 64 128 256), losses := [] }

theorem u13126 : Upper (D 8) (R 8) [96,5,129,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13127 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 88 304 170 234 170 426), lower := (rows 97 7 133 88 304 32 64 128 256), losses := [] }

theorem u13127 : Upper (D 8) (R 8) [96,5,129,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13128 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 88 400 42 106 170 298), lower := (rows 97 7 133 88 400 32 64 128 256), losses := [] }

theorem u13128 : Upper (D 8) (R 8) [96,5,129,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13129 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 138 280 112 112 240 368), lower := (rows 97 7 133 138 280 32 64 128 256), losses := [] }

theorem u13129 : Upper (D 8) (R 8) [96,5,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13130 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 138 304 120 120 248 376), lower := (rows 97 7 133 138 304 32 64 128 256), losses := [] }

theorem u13130 : Upper (D 8) (R 8) [96,5,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13131 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 138 336 56 120 184 312), lower := (rows 97 7 133 138 336 32 64 128 256), losses := [] }

theorem u13131 : Upper (D 8) (R 8) [96,5,129,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13132 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 152 274 104 104 232 360), lower := (rows 97 7 133 152 274 32 64 128 256), losses := [] }

theorem u13132 : Upper (D 8) (R 8) [96,5,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13133 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 133 152 280 98 98 226 354), lower := (rows 97 7 133 152 280 32 64 128 256), losses := [] }

theorem u13133 : Upper (D 8) (R 8) [96,5,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13134 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 152 304 106 106 234 362), lower := (rows 97 7 133 152 304 32 64 128 256), losses := [] }

theorem u13134 : Upper (D 8) (R 8) [96,5,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13135 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 152 336 42 106 170 298), lower := (rows 97 7 133 152 336 32 64 128 256), losses := [] }

theorem u13135 : Upper (D 8) (R 8) [96,5,129,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13136 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 274 120 120 248 376), lower := (rows 97 7 133 168 274 32 64 128 256), losses := [] }

theorem u13136 : Upper (D 8) (R 8) [96,5,129,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13137 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 280 114 114 242 370), lower := (rows 97 7 133 168 280 32 64 128 256), losses := [] }

theorem u13137 : Upper (D 8) (R 8) [96,5,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13138 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 304 122 90 218 346), lower := (rows 97 7 133 168 304 32 64 128 256), losses := [] }

theorem u13138 : Upper (D 8) (R 8) [96,5,129,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13139 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 336 58 122 186 314), lower := (rows 97 7 133 168 336 32 64 128 256), losses := [] }

theorem u13139 : Upper (D 8) (R 8) [96,5,129,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13139
end Delivery.IrregularNine14.P08
