import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0335

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35100 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 56 84 425 457 393 393), lower := (rows 35 194 7 56 84 32 64 128 256), losses := [] }

theorem u35100 : Upper (D 7) (R 7) [34,192,3,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35101 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 56 273 236 204 204 460), lower := (rows 35 194 7 56 273 32 64 128 256), losses := [] }

theorem u35101 : Upper (D 7) (R 7) [34,192,3,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35102 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 56 276 233 201 201 457), lower := (rows 35 194 7 56 276 32 64 128 256), losses := [] }

theorem u35102 : Upper (D 7) (R 7) [34,192,3,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35103 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 0, region := 4, targets := 192 }], pairs := [(1,5),(2,5),(2,6),(2,7)], upper := (rows 35 194 7 56 280 229 197 197 453), lower := (rows 35 194 7 56 280 32 64 128 256), losses := [] }

theorem u35103 : Upper (D 7) (R 7) [34,192,3,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35104 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 56 336 173 205 141 397), lower := (rows 35 194 7 56 336 32 64 128 256), losses := [] }

theorem u35104 : Upper (D 7) (R 7) [34,192,3,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35105 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 73 148 312 376 440 312), lower := (rows 35 194 7 73 148 32 64 128 256), losses := [] }

theorem u35105 : Upper (D 7) (R 7) [34,192,3,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35106 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 73 152 308 372 436 308), lower := (rows 35 194 7 73 152 32 64 128 256), losses := [] }

theorem u35106 : Upper (D 7) (R 7) [34,192,3,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35107 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 73 176 316 348 412 284), lower := (rows 35 194 7 73 176 32 64 128 256), losses := [] }

theorem u35107 : Upper (D 7) (R 7) [34,192,3,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35108 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 73 276 184 248 184 440), lower := (rows 35 194 7 73 276 32 64 128 256), losses := [] }

theorem u35108 : Upper (D 7) (R 7) [34,192,3,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35109 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 73 280 180 244 180 436), lower := (rows 35 194 7 73 280 32 64 128 256), losses := [] }

theorem u35109 : Upper (D 7) (R 7) [34,192,3,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35110 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 73 304 188 220 156 412), lower := (rows 35 194 7 73 304 32 64 128 256), losses := [] }

theorem u35110 : Upper (D 7) (R 7) [34,192,3,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35111 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 73 400 60 124 188 316), lower := (rows 35 194 7 73 400 32 64 128 256), losses := [] }

theorem u35111 : Upper (D 7) (R 7) [34,192,3,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35112 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 76 152 305 369 433 305), lower := (rows 35 194 7 76 152 32 64 128 256), losses := [] }

theorem u35112 : Upper (D 7) (R 7) [34,192,3,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35113 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 76 176 313 345 409 281), lower := (rows 35 194 7 76 176 32 64 128 256), losses := [] }

theorem u35113 : Upper (D 7) (R 7) [34,192,3,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35114 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 76 273 184 248 184 440), lower := (rows 35 194 7 76 273 32 64 128 256), losses := [] }

theorem u35114 : Upper (D 7) (R 7) [34,192,3,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35115 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 76 280 177 241 177 433), lower := (rows 35 194 7 76 280 32 64 128 256), losses := [] }

theorem u35115 : Upper (D 7) (R 7) [34,192,3,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35116 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 76 304 185 217 153 409), lower := (rows 35 194 7 76 304 32 64 128 256), losses := [] }

theorem u35116 : Upper (D 7) (R 7) [34,192,3,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35117 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 76 400 57 121 185 313), lower := (rows 35 194 7 76 400 32 64 128 256), losses := [] }

theorem u35117 : Upper (D 7) (R 7) [34,192,3,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35118 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 88 176 301 333 397 269), lower := (rows 35 194 7 88 176 32 64 128 256), losses := [] }

theorem u35118 : Upper (D 7) (R 7) [34,192,3,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35119 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 88 273 172 236 172 428), lower := (rows 35 194 7 88 273 32 64 128 256), losses := [] }

theorem u35119 : Upper (D 7) (R 7) [34,192,3,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35120 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 88 276 169 233 169 425), lower := (rows 35 194 7 88 276 32 64 128 256), losses := [] }

theorem u35120 : Upper (D 7) (R 7) [34,192,3,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35121 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 4, targets := 160 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(2,5),(2,6),(2,7)], upper := (rows 35 194 7 88 280 165 229 165 421), lower := (rows 35 194 7 88 280 32 64 128 256), losses := [] }

theorem u35121 : Upper (D 7) (R 7) [34,192,3,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35122 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 88 304 173 205 141 397), lower := (rows 35 194 7 88 304 32 64 128 256), losses := [] }

theorem u35122 : Upper (D 7) (R 7) [34,192,3,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35123 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 88 400 45 109 173 301), lower := (rows 35 194 7 88 400 32 64 128 256), losses := [] }

theorem u35123 : Upper (D 7) (R 7) [34,192,3,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35124 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 104 273 188 220 156 412), lower := (rows 35 194 7 104 273 32 64 128 256), losses := [] }

theorem u35124 : Upper (D 7) (R 7) [34,192,3,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35125 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 104 276 185 217 153 409), lower := (rows 35 194 7 104 276 32 64 128 256), losses := [] }

theorem u35125 : Upper (D 7) (R 7) [34,192,3,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35126 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 104 280 181 213 149 405), lower := (rows 35 194 7 104 280 32 64 128 256), losses := [] }

theorem u35126 : Upper (D 7) (R 7) [34,192,3,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35127 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 104 400 61 93 157 285), lower := (rows 35 194 7 104 400 32 64 128 256), losses := [] }

theorem u35127 : Upper (D 7) (R 7) [34,192,3,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35128 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 13 112 434 466 402 402), lower := (rows 35 194 13 13 112 32 64 128 256), losses := [] }

theorem u35128 : Upper (D 7) (R 7) [34,192,9,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35129 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 13 274 240 240 240 496), lower := (rows 35 194 13 13 274 32 64 128 256), losses := [] }

theorem u35129 : Upper (D 7) (R 7) [34,192,9,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35130 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 13 304 242 210 210 466), lower := (rows 35 194 13 13 304 32 64 128 256), losses := [] }

theorem u35130 : Upper (D 7) (R 7) [34,192,9,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35131 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 13 336 178 242 178 434), lower := (rows 35 194 13 13 336 32 64 128 256), losses := [] }

theorem u35131 : Upper (D 7) (R 7) [34,192,9,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35132 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 13 14 81 432 496 432 432), lower := (rows 35 194 13 14 81 32 64 128 256), losses := [] }

theorem u35132 : Upper (D 7) (R 7) [34,192,9,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35133 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 13 14 112 433 465 401 401), lower := (rows 35 194 13 14 112 32 64 128 256), losses := [] }

theorem u35133 : Upper (D 7) (R 7) [34,192,9,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35134 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 13 14 273 240 240 240 496), lower := (rows 35 194 13 14 273 32 64 128 256), losses := [] }

theorem u35134 : Upper (D 7) (R 7) [34,192,9,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35135 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 13 14 304 241 209 209 465), lower := (rows 35 194 13 14 304 32 64 128 256), losses := [] }

theorem u35135 : Upper (D 7) (R 7) [34,192,9,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35136 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 13 14 336 177 241 177 433), lower := (rows 35 194 13 14 336 32 64 128 256), losses := [] }

theorem u35136 : Upper (D 7) (R 7) [34,192,9,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35137 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 28, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 13 25 22 480 480 480 480), lower := (rows 35 194 13 25 22 32 64 128 256), losses := [] }

theorem u35137 : Upper (D 7) (R 7) [34,192,9,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35138 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 28, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 25 52 482 450 450 450), lower := (rows 35 194 13 25 52 32 64 128 256), losses := [] }

theorem u35138 : Upper (D 7) (R 7) [34,192,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35139 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 25 84 418 482 418 418), lower := (rows 35 194 13 25 84 32 64 128 256), losses := [] }

theorem u35139 : Upper (D 7) (R 7) [34,192,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35140 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 4, targets := 194 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 35 194 13 25 112 422 454 390 390), lower := (rows 35 194 13 25 112 32 64 128 256), losses := [] }

theorem u35140 : Upper (D 7) (R 7) [34,192,9,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35141 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 224 },{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 25 274 228 228 228 484), lower := (rows 35 194 13 25 274 32 64 128 256), losses := [] }

theorem u35141 : Upper (D 7) (R 7) [34,192,9,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35142 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 25 276 226 226 226 482), lower := (rows 35 194 13 25 276 32 64 128 256), losses := [] }

theorem u35142 : Upper (D 7) (R 7) [34,192,9,17,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35143 : PairBound 9 := { available := 198, camps := [{ cop := 3, region := 4, targets := 194 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 35 194 13 25 304 230 198 198 454), lower := (rows 35 194 13 25 304 32 64 128 256), losses := [] }

theorem u35143 : Upper (D 7) (R 7) [34,192,9,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35144 : PairBound 9 := { available := 166, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 25 336 166 230 166 422), lower := (rows 35 194 13 25 336 32 64 128 256), losses := [] }

theorem u35144 : Upper (D 7) (R 7) [34,192,9,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35145 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 26 49 484 452 452 452), lower := (rows 35 194 13 26 49 32 64 128 256), losses := [] }

theorem u35145 : Upper (D 7) (R 7) [34,192,9,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35146 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 26 52 481 449 449 449), lower := (rows 35 194 13 26 52 32 64 128 256), losses := [] }

theorem u35146 : Upper (D 7) (R 7) [34,192,9,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35147 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 2, region := 482, targets := 1 },{ cop := 2, region := 496, targets := 2 }], pairs := [(0,6),(1,0),(2,6),(4,1)], upper := (rows 35 194 13 26 81 420 484 420 420), lower := (rows 35 194 13 26 81 32 64 128 256), losses := [] }

theorem u35147 : Upper (D 7) (R 7) [34,192,9,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35148 : Route 9 := (fun mask => (mask,id))

def c35148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35148 : Upper (D 7) (R 7) [34,192,9,18,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,18,68] 13 (by decide) (choices 1) [1,128,256] r35148 c35148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20131
  · exact u20132
  · exact u20133

def b35149 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 2, region := 496, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,1)], upper := (rows 35 194 13 26 112 421 453 389 389), lower := (rows 35 194 13 26 112 32 64 128 256), losses := [] }

theorem u35149 : Upper (D 7) (R 7) [34,192,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35150 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 194 13 26 208 293 357 421 293), lower := (rows 35 194 13 26 208 32 64 128 256), losses := [] }

theorem u35150 : Upper (D 7) (R 7) [34,192,9,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35151 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35151 : Upper (D 7) (R 7) [34,192,9,18,257] 13 := by
  apply FastRouting.sound _ _ [34,192,9,18,257] 13 (by decide) (choices 1) [4,64] r35151 c35151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20134
  · exact u20135

def r35152 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35152 : Upper (D 7) (R 7) [34,192,9,18,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,18,260] 13 (by decide) (choices 1) [1,64] r35152 c35152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20136
  · exact u20137

def r35153 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35153 : Upper (D 7) (R 7) [34,192,9,18,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,18,288] 13 (by decide) (choices 1) [1,4,64] r35153 c35153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20138
  · exact u20139
  · exact u20140

def r35154 : Route 9 := (fun mask => (mask,id))

def c35154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35154 : Upper (D 7) (R 7) [34,192,9,18,320] 13 := by
  apply FastRouting.sound _ _ [34,192,9,18,320] 13 (by decide) (choices 1) [1,4,128] r35154 c35154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20141
  · exact u20142
  · exact u20143

def b35155 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 28, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 28 49 482 450 450 450), lower := (rows 35 194 13 28 49 32 64 128 256), losses := [] }

theorem u35155 : Upper (D 7) (R 7) [34,192,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35156 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 28 50 481 449 449 449), lower := (rows 35 194 13 28 50 32 64 128 256), losses := [] }

theorem u35156 : Upper (D 7) (R 7) [34,192,9,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35157 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 28 81 418 482 418 418), lower := (rows 35 194 13 28 81 32 64 128 256), losses := [] }

theorem u35157 : Upper (D 7) (R 7) [34,192,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35158 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 194 13 28 82 417 481 417 417), lower := (rows 35 194 13 28 82 32 64 128 256), losses := [] }

theorem u35158 : Upper (D 7) (R 7) [34,192,9,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35159 : Route 9 := (fun mask => (mask,id))

def c35159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u35159 : Upper (D 7) (R 7) [34,192,9,20,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,96] 13 (by decide) (choices 1) [1,2,128,256] r35159 c35159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20144
  · exact u20145
  · exact u20146
  · exact u20147

#print axioms u35159
end Delivery.IrregularNine14.P07
