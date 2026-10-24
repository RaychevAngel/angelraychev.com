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

def b14340 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 266 145 244 212 212 468), lower := (rows 97 35 44 266 145 32 64 128 256), losses := [] }

theorem u14340 : Upper (D 8) (R 8) [96,33,40,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14341 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 266 148 241 209 209 465), lower := (rows 97 35 44 266 148 32 64 128 256), losses := [] }

theorem u14341 : Upper (D 8) (R 8) [96,33,40,258,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14342 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 266 208 181 213 149 405), lower := (rows 97 35 44 266 208 32 64 128 256), losses := [] }

theorem u14342 : Upper (D 8) (R 8) [96,33,40,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14343 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 268 82 177 209 145 401), lower := (rows 97 35 44 268 82 32 64 128 256), losses := [] }

theorem u14343 : Upper (D 8) (R 8) [96,33,40,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14344 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 268 145 242 210 210 466), lower := (rows 97 35 44 268 145 32 64 128 256), losses := [] }

theorem u14344 : Upper (D 8) (R 8) [96,33,40,260,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14345 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 268 146 241 209 209 465), lower := (rows 97 35 44 268 146 32 64 128 256), losses := [] }

theorem u14345 : Upper (D 8) (R 8) [96,33,40,260,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14346 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 268 208 179 211 147 403), lower := (rows 97 35 44 268 208 32 64 128 256), losses := [] }

theorem u14346 : Upper (D 8) (R 8) [96,33,40,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14347 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 280 82 165 197 133 389), lower := (rows 97 35 44 280 82 32 64 128 256), losses := [] }

theorem u14347 : Upper (D 8) (R 8) [96,33,40,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14348 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 280 145 230 198 198 454), lower := (rows 97 35 44 280 145 32 64 128 256), losses := [] }

theorem u14348 : Upper (D 8) (R 8) [96,33,40,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14349 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 280 146 229 197 197 453), lower := (rows 97 35 44 280 146 32 64 128 256), losses := [] }

theorem u14349 : Upper (D 8) (R 8) [96,33,40,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14350 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 280 148 227 195 195 451), lower := (rows 97 35 44 280 148 32 64 128 256), losses := [] }

theorem u14350 : Upper (D 8) (R 8) [96,33,40,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14351 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 280 208 167 199 135 391), lower := (rows 97 35 44 280 208 32 64 128 256), losses := [] }

theorem u14351 : Upper (D 8) (R 8) [96,33,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14352 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 328 145 182 214 150 406), lower := (rows 97 35 44 328 145 32 64 128 256), losses := [] }

theorem u14352 : Upper (D 8) (R 8) [96,33,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14353 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 328 146 181 213 149 405), lower := (rows 97 35 44 328 146 32 64 128 256), losses := [] }

theorem u14353 : Upper (D 8) (R 8) [96,33,40,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14354 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 328 148 179 211 147 403), lower := (rows 97 35 44 328 148 32 64 128 256), losses := [] }

theorem u14354 : Upper (D 8) (R 8) [96,33,40,320,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14355 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 392 82 181 213 149 405), lower := (rows 97 35 44 392 82 32 64 128 256), losses := [] }

theorem u14355 : Upper (D 8) (R 8) [96,33,40,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14356 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 392 84 179 211 147 403), lower := (rows 97 35 44 392 84 32 64 128 256), losses := [] }

theorem u14356 : Upper (D 8) (R 8) [96,33,40,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14357 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 392 145 118 86 214 342), lower := (rows 97 35 44 392 145 32 64 128 256), losses := [] }

theorem u14357 : Upper (D 8) (R 8) [96,33,40,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14358 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 392 146 117 85 213 341), lower := (rows 97 35 44 392 146 32 64 128 256), losses := [] }

theorem u14358 : Upper (D 8) (R 8) [96,33,40,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14359 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 392 208 55 87 151 279), lower := (rows 97 35 44 392 208 32 64 128 256), losses := [] }

theorem u14359 : Upper (D 8) (R 8) [96,33,40,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14360 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 137 148 312 376 440 312), lower := (rows 97 35 70 137 148 32 64 128 256), losses := [] }

theorem u14360 : Upper (D 8) (R 8) [96,33,66,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14361 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 137 176 316 348 412 284), lower := (rows 97 35 70 137 176 32 64 128 256), losses := [] }

theorem u14361 : Upper (D 8) (R 8) [96,33,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14362 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 137 276 184 248 184 440), lower := (rows 97 35 70 137 276 32 64 128 256), losses := [] }

theorem u14362 : Upper (D 8) (R 8) [96,33,66,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14363 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 137 280 180 244 180 436), lower := (rows 97 35 70 137 280 32 64 128 256), losses := [] }

theorem u14363 : Upper (D 8) (R 8) [96,33,66,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14364 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 137 304 188 220 156 412), lower := (rows 97 35 70 137 304 32 64 128 256), losses := [] }

theorem u14364 : Upper (D 8) (R 8) [96,33,66,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14365 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 137 400 60 124 188 316), lower := (rows 97 35 70 137 400 32 64 128 256), losses := [] }

theorem u14365 : Upper (D 8) (R 8) [96,33,66,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14366 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 140 176 313 345 409 281), lower := (rows 97 35 70 140 176 32 64 128 256), losses := [] }

theorem u14366 : Upper (D 8) (R 8) [96,33,66,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14367 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 140 273 184 248 184 440), lower := (rows 97 35 70 140 273 32 64 128 256), losses := [] }

theorem u14367 : Upper (D 8) (R 8) [96,33,66,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14368 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 140 280 177 241 177 433), lower := (rows 97 35 70 140 280 32 64 128 256), losses := [] }

theorem u14368 : Upper (D 8) (R 8) [96,33,66,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14369 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 140 304 185 217 153 409), lower := (rows 97 35 70 140 304 32 64 128 256), losses := [] }

theorem u14369 : Upper (D 8) (R 8) [96,33,66,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14370 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 140 400 57 121 185 313), lower := (rows 97 35 70 140 400 32 64 128 256), losses := [] }

theorem u14370 : Upper (D 8) (R 8) [96,33,66,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14371 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 152 273 172 236 172 428), lower := (rows 97 35 70 152 273 32 64 128 256), losses := [] }

theorem u14371 : Upper (D 8) (R 8) [96,33,66,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14372 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 152 276 169 233 169 425), lower := (rows 97 35 70 152 276 32 64 128 256), losses := [] }

theorem u14372 : Upper (D 8) (R 8) [96,33,66,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14373 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 152 280 165 229 165 421), lower := (rows 97 35 70 152 280 32 64 128 256), losses := [] }

theorem u14373 : Upper (D 8) (R 8) [96,33,66,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14374 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 152 304 173 205 141 397), lower := (rows 97 35 70 152 304 32 64 128 256), losses := [] }

theorem u14374 : Upper (D 8) (R 8) [96,33,66,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14375 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 168 273 188 220 156 412), lower := (rows 97 35 70 168 273 32 64 128 256), losses := [] }

theorem u14375 : Upper (D 8) (R 8) [96,33,66,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14376 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 168 276 185 217 153 409), lower := (rows 97 35 70 168 276 32 64 128 256), losses := [] }

theorem u14376 : Upper (D 8) (R 8) [96,33,66,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14377 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 168 280 181 213 149 405), lower := (rows 97 35 70 168 280 32 64 128 256), losses := [] }

theorem u14377 : Upper (D 8) (R 8) [96,33,66,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14378 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 168 400 61 93 157 285), lower := (rows 97 35 70 168 400 32 64 128 256), losses := [] }

theorem u14378 : Upper (D 8) (R 8) [96,33,66,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14379 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 137 146 308 372 436 308), lower := (rows 97 35 76 137 146 32 64 128 256), losses := [] }

theorem u14379 : Upper (D 8) (R 8) [96,33,72,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14380 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 137 176 310 342 406 278), lower := (rows 97 35 76 137 176 32 64 128 256), losses := [] }

theorem u14380 : Upper (D 8) (R 8) [96,33,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14381 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 137 274 180 244 180 436), lower := (rows 97 35 76 137 274 32 64 128 256), losses := [] }

theorem u14381 : Upper (D 8) (R 8) [96,33,72,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14382 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 137 276 178 242 178 434), lower := (rows 97 35 76 137 276 32 64 128 256), losses := [] }

theorem u14382 : Upper (D 8) (R 8) [96,33,72,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14383 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 137 304 182 214 150 406), lower := (rows 97 35 76 137 304 32 64 128 256), losses := [] }

theorem u14383 : Upper (D 8) (R 8) [96,33,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14384 : PairBound 9 := { available := 54, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 137 400 54 118 182 310), lower := (rows 97 35 76 137 400 32 64 128 256), losses := [] }

theorem u14384 : Upper (D 8) (R 8) [96,33,72,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14385 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 138 145 308 372 436 308), lower := (rows 97 35 76 138 145 32 64 128 256), losses := [] }

theorem u14385 : Upper (D 8) (R 8) [96,33,72,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14386 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 138 176 309 341 405 277), lower := (rows 97 35 76 138 176 32 64 128 256), losses := [] }

theorem u14386 : Upper (D 8) (R 8) [96,33,72,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14387 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 138 273 180 244 180 436), lower := (rows 97 35 76 138 273 32 64 128 256), losses := [] }

theorem u14387 : Upper (D 8) (R 8) [96,33,72,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14388 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 138 276 177 241 177 433), lower := (rows 97 35 76 138 276 32 64 128 256), losses := [] }

theorem u14388 : Upper (D 8) (R 8) [96,33,72,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14389 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 138 304 181 213 149 405), lower := (rows 97 35 76 138 304 32 64 128 256), losses := [] }

theorem u14389 : Upper (D 8) (R 8) [96,33,72,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14390 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 138 400 53 117 181 309), lower := (rows 97 35 76 138 400 32 64 128 256), losses := [] }

theorem u14390 : Upper (D 8) (R 8) [96,33,72,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14391 : PairBound 9 := { available := 166, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 152 273 166 230 166 422), lower := (rows 97 35 76 152 273 32 64 128 256), losses := [] }

theorem u14391 : Upper (D 8) (R 8) [96,33,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14392 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 152 274 165 229 165 421), lower := (rows 97 35 76 152 274 32 64 128 256), losses := [] }

theorem u14392 : Upper (D 8) (R 8) [96,33,72,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14393 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 152 304 167 199 135 391), lower := (rows 97 35 76 152 304 32 64 128 256), losses := [] }

theorem u14393 : Upper (D 8) (R 8) [96,33,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14394 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 168 145 310 342 406 278), lower := (rows 97 35 76 168 145 32 64 128 256), losses := [] }

theorem u14394 : Upper (D 8) (R 8) [96,33,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14395 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 168 146 309 341 405 277), lower := (rows 97 35 76 168 146 32 64 128 256), losses := [] }

theorem u14395 : Upper (D 8) (R 8) [96,33,72,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14396 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 168 273 182 214 150 406), lower := (rows 97 35 76 168 273 32 64 128 256), losses := [] }

theorem u14396 : Upper (D 8) (R 8) [96,33,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14397 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 168 274 181 213 149 405), lower := (rows 97 35 76 168 274 32 64 128 256), losses := [] }

theorem u14397 : Upper (D 8) (R 8) [96,33,72,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14398 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 168 276 179 211 147 403), lower := (rows 97 35 76 168 276 32 64 128 256), losses := [] }

theorem u14398 : Upper (D 8) (R 8) [96,33,72,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14399 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 168 400 55 87 151 279), lower := (rows 97 35 76 168 400 32 64 128 256), losses := [] }

theorem u14399 : Upper (D 8) (R 8) [96,33,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14399
end Delivery.IrregularNine14.P08
