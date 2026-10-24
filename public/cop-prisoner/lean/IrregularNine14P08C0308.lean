import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0113

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18480 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 164 200 50 49 113 177 305), lower := (rows 321 14 164 200 50 32 64 128 256), losses := [] }

theorem u18480 : Upper (D 8) (R 8) [320,12,160,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18481 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 42 84 184 216 152 408), lower := (rows 321 35 37 42 84 32 64 128 256), losses := [] }

theorem u18481 : Upper (D 8) (R 8) [320,33,33,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18482 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 42 88 180 212 148 404), lower := (rows 321 35 37 42 88 32 64 128 256), losses := [] }

theorem u18482 : Upper (D 8) (R 8) [320,33,33,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18483 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 42 148 248 216 216 472), lower := (rows 321 35 37 42 148 32 64 128 256), losses := [] }

theorem u18483 : Upper (D 8) (R 8) [320,33,33,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18484 : PairBound 9 := { available := 212, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 42 152 244 212 212 468), lower := (rows 321 35 37 42 152 32 64 128 256), losses := [] }

theorem u18484 : Upper (D 8) (R 8) [320,33,33,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18485 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 42 208 188 220 156 412), lower := (rows 321 35 37 42 208 32 64 128 256), losses := [] }

theorem u18485 : Upper (D 8) (R 8) [320,33,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18486 : PairBound 9 := { available := 140, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 56 82 172 204 140 396), lower := (rows 321 35 37 56 82 32 64 128 256), losses := [] }

theorem u18486 : Upper (D 8) (R 8) [320,33,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18487 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 56 146 236 204 204 460), lower := (rows 321 35 37 56 146 32 64 128 256), losses := [] }

theorem u18487 : Upper (D 8) (R 8) [320,33,33,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18488 : PairBound 9 := { available := 198, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 56 152 230 198 198 454), lower := (rows 321 35 37 56 152 32 64 128 256), losses := [] }

theorem u18488 : Upper (D 8) (R 8) [320,33,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18489 : PairBound 9 := { available := 142, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 56 208 174 206 142 398), lower := (rows 321 35 37 56 208 32 64 128 256), losses := [] }

theorem u18489 : Upper (D 8) (R 8) [320,33,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18490 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 74 148 184 248 184 440), lower := (rows 321 35 37 74 148 32 64 128 256), losses := [] }

theorem u18490 : Upper (D 8) (R 8) [320,33,33,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18491 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 74 152 180 244 180 436), lower := (rows 321 35 37 74 152 32 64 128 256), losses := [] }

theorem u18491 : Upper (D 8) (R 8) [320,33,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18492 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 74 176 188 220 156 412), lower := (rows 321 35 37 74 176 32 64 128 256), losses := [] }

theorem u18492 : Upper (D 8) (R 8) [320,33,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18493 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 88 146 172 236 172 428), lower := (rows 321 35 37 88 146 32 64 128 256), losses := [] }

theorem u18493 : Upper (D 8) (R 8) [320,33,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18494 : PairBound 9 := { available := 142, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 88 176 174 206 142 398), lower := (rows 321 35 37 88 176 32 64 128 256), losses := [] }

theorem u18494 : Upper (D 8) (R 8) [320,33,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18495 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 104 146 188 220 156 412), lower := (rows 321 35 37 104 146 32 64 128 256), losses := [] }

theorem u18495 : Upper (D 8) (R 8) [320,33,33,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18496 : PairBound 9 := { available := 150, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 104 152 182 214 150 406), lower := (rows 321 35 37 104 152 32 64 128 256), losses := [] }

theorem u18496 : Upper (D 8) (R 8) [320,33,33,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18497 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 138 148 120 120 248 376), lower := (rows 321 35 37 138 148 32 64 128 256), losses := [] }

theorem u18497 : Upper (D 8) (R 8) [320,33,33,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18498 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 138 176 124 92 220 348), lower := (rows 321 35 37 138 176 32 64 128 256), losses := [] }

theorem u18498 : Upper (D 8) (R 8) [320,33,33,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18499 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 138 208 60 124 188 316), lower := (rows 321 35 37 138 208 32 64 128 256), losses := [] }

theorem u18499 : Upper (D 8) (R 8) [320,33,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18500 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 321 35 37 168 208 62 94 158 286), lower := (rows 321 35 37 168 208 32 64 128 256), losses := [] }

theorem u18500 : Upper (D 8) (R 8) [320,33,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18501 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 44 88 177 209 145 401), lower := (rows 321 35 38 44 88 32 64 128 256), losses := [] }

theorem u18501 : Upper (D 8) (R 8) [320,33,34,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18502 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 44 145 248 216 216 472), lower := (rows 321 35 38 44 145 32 64 128 256), losses := [] }

theorem u18502 : Upper (D 8) (R 8) [320,33,34,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18503 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 44 152 241 209 209 465), lower := (rows 321 35 38 44 152 32 64 128 256), losses := [] }

theorem u18503 : Upper (D 8) (R 8) [320,33,34,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18504 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 44 208 185 217 153 409), lower := (rows 321 35 38 44 208 32 64 128 256), losses := [] }

theorem u18504 : Upper (D 8) (R 8) [320,33,34,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18505 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 56 84 169 201 137 393), lower := (rows 321 35 38 56 84 32 64 128 256), losses := [] }

theorem u18505 : Upper (D 8) (R 8) [320,33,34,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18506 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 56 145 236 204 204 460), lower := (rows 321 35 38 56 145 32 64 128 256), losses := [] }

theorem u18506 : Upper (D 8) (R 8) [320,33,34,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18507 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 56 148 233 201 201 457), lower := (rows 321 35 38 56 148 32 64 128 256), losses := [] }

theorem u18507 : Upper (D 8) (R 8) [320,33,34,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18508 : PairBound 9 := { available := 197, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 56 152 229 197 197 453), lower := (rows 321 35 38 56 152 32 64 128 256), losses := [] }

theorem u18508 : Upper (D 8) (R 8) [320,33,34,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18509 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 56 208 173 205 141 397), lower := (rows 321 35 38 56 208 32 64 128 256), losses := [] }

theorem u18509 : Upper (D 8) (R 8) [320,33,34,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18510 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 76 145 184 248 184 440), lower := (rows 321 35 38 76 145 32 64 128 256), losses := [] }

theorem u18510 : Upper (D 8) (R 8) [320,33,34,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18511 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 76 152 177 241 177 433), lower := (rows 321 35 38 76 152 32 64 128 256), losses := [] }

theorem u18511 : Upper (D 8) (R 8) [320,33,34,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18512 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 76 176 185 217 153 409), lower := (rows 321 35 38 76 176 32 64 128 256), losses := [] }

theorem u18512 : Upper (D 8) (R 8) [320,33,34,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18513 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 88 145 172 236 172 428), lower := (rows 321 35 38 88 145 32 64 128 256), losses := [] }

theorem u18513 : Upper (D 8) (R 8) [320,33,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18514 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 88 148 169 233 169 425), lower := (rows 321 35 38 88 148 32 64 128 256), losses := [] }

theorem u18514 : Upper (D 8) (R 8) [320,33,34,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18515 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 88 176 173 205 141 397), lower := (rows 321 35 38 88 176 32 64 128 256), losses := [] }

theorem u18515 : Upper (D 8) (R 8) [320,33,34,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18516 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 104 145 188 220 156 412), lower := (rows 321 35 38 104 145 32 64 128 256), losses := [] }

theorem u18516 : Upper (D 8) (R 8) [320,33,34,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18517 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 104 148 185 217 153 409), lower := (rows 321 35 38 104 148 32 64 128 256), losses := [] }

theorem u18517 : Upper (D 8) (R 8) [320,33,34,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18518 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 104 152 181 213 149 405), lower := (rows 321 35 38 104 152 32 64 128 256), losses := [] }

theorem u18518 : Upper (D 8) (R 8) [320,33,34,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18519 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 137 148 120 120 248 376), lower := (rows 321 35 38 137 148 32 64 128 256), losses := [] }

theorem u18519 : Upper (D 8) (R 8) [320,33,34,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18520 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 137 176 124 92 220 348), lower := (rows 321 35 38 137 176 32 64 128 256), losses := [] }

theorem u18520 : Upper (D 8) (R 8) [320,33,34,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18521 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 137 208 60 124 188 316), lower := (rows 321 35 38 137 208 32 64 128 256), losses := [] }

theorem u18521 : Upper (D 8) (R 8) [320,33,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18522 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 140 176 121 89 217 345), lower := (rows 321 35 38 140 176 32 64 128 256), losses := [] }

theorem u18522 : Upper (D 8) (R 8) [320,33,34,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18523 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 140 208 57 121 185 313), lower := (rows 321 35 38 140 208 32 64 128 256), losses := [] }

theorem u18523 : Upper (D 8) (R 8) [320,33,34,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18524 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 38 168 208 61 93 157 285), lower := (rows 321 35 38 168 208 32 64 128 256), losses := [] }

theorem u18524 : Upper (D 8) (R 8) [320,33,34,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18525 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 44 82 177 209 145 401), lower := (rows 321 35 44 44 82 32 64 128 256), losses := [] }

theorem u18525 : Upper (D 8) (R 8) [320,33,40,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18526 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 44 145 242 210 210 466), lower := (rows 321 35 44 44 145 32 64 128 256), losses := [] }

theorem u18526 : Upper (D 8) (R 8) [320,33,40,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18527 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 44 146 241 209 209 465), lower := (rows 321 35 44 44 146 32 64 128 256), losses := [] }

theorem u18527 : Upper (D 8) (R 8) [320,33,40,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18528 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 44 208 179 211 147 403), lower := (rows 321 35 44 44 208 32 64 128 256), losses := [] }

theorem u18528 : Upper (D 8) (R 8) [320,33,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18529 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 56 82 165 197 133 389), lower := (rows 321 35 44 56 82 32 64 128 256), losses := [] }

theorem u18529 : Upper (D 8) (R 8) [320,33,40,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18530 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 56 84 163 195 131 387), lower := (rows 321 35 44 56 84 32 64 128 256), losses := [] }

theorem u18530 : Upper (D 8) (R 8) [320,33,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18531 : PairBound 9 := { available := 198, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 56 145 230 198 198 454), lower := (rows 321 35 44 56 145 32 64 128 256), losses := [] }

theorem u18531 : Upper (D 8) (R 8) [320,33,40,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18532 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 56 146 229 197 197 453), lower := (rows 321 35 44 56 146 32 64 128 256), losses := [] }

theorem u18532 : Upper (D 8) (R 8) [320,33,40,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18533 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 56 148 227 195 195 451), lower := (rows 321 35 44 56 148 32 64 128 256), losses := [] }

theorem u18533 : Upper (D 8) (R 8) [320,33,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18534 : PairBound 9 := { available := 135, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 35 44 56 208 167 199 135 391), lower := (rows 321 35 44 56 208 32 64 128 256), losses := [] }

theorem u18534 : Upper (D 8) (R 8) [320,33,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18535 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 73 146 180 244 180 436), lower := (rows 321 35 44 73 146 32 64 128 256), losses := [] }

theorem u18535 : Upper (D 8) (R 8) [320,33,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18536 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 73 148 178 242 178 434), lower := (rows 321 35 44 73 148 32 64 128 256), losses := [] }

theorem u18536 : Upper (D 8) (R 8) [320,33,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18537 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 35 44 73 176 182 214 150 406), lower := (rows 321 35 44 73 176 32 64 128 256), losses := [] }

theorem u18537 : Upper (D 8) (R 8) [320,33,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18538 : Route 9 := (fun mask => (mask,id))

def c18538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18538 : Upper (D 8) (R 8) [320,33,40,66,129] 13 := by
  apply FastRouting.sound _ _ [320,33,40,66,129] 13 (by decide) (choices 1) [4,16,128] r18538 c18538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6830
  · exact u6831
  · exact u6832

def r18539 : Route 9 := (fun mask => (mask,id))

def c18539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18539 : Upper (D 8) (R 8) [320,33,40,66,132] 13 := by
  apply FastRouting.sound _ _ [320,33,40,66,132] 13 (by decide) (choices 1) [1,16,128] r18539 c18539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6833
  · exact u6834
  · exact u6835

#print axioms u18539
end Delivery.IrregularNine14.P08
