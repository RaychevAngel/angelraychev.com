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

def b14280 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 137 400 124 92 220 348), lower := (rows 97 35 38 137 400 32 64 128 256), losses := [] }

theorem u14280 : Upper (D 8) (R 8) [96,33,34,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14281 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 140 208 313 345 409 281), lower := (rows 97 35 38 140 208 32 64 128 256), losses := [] }

theorem u14281 : Upper (D 8) (R 8) [96,33,34,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14282 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 140 273 248 216 216 472), lower := (rows 97 35 38 140 273 32 64 128 256), losses := [] }

theorem u14282 : Upper (D 8) (R 8) [96,33,34,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14283 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 140 280 241 209 209 465), lower := (rows 97 35 38 140 280 32 64 128 256), losses := [] }

theorem u14283 : Upper (D 8) (R 8) [96,33,34,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14284 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 140 336 185 217 153 409), lower := (rows 97 35 38 140 336 32 64 128 256), losses := [] }

theorem u14284 : Upper (D 8) (R 8) [96,33,34,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14285 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 140 400 121 89 217 345), lower := (rows 97 35 38 140 400 32 64 128 256), losses := [] }

theorem u14285 : Upper (D 8) (R 8) [96,33,34,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14286 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 152 273 236 204 204 460), lower := (rows 97 35 38 152 273 32 64 128 256), losses := [] }

theorem u14286 : Upper (D 8) (R 8) [96,33,34,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14287 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 152 276 233 201 201 457), lower := (rows 97 35 38 152 276 32 64 128 256), losses := [] }

theorem u14287 : Upper (D 8) (R 8) [96,33,34,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14288 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 152 280 229 197 197 453), lower := (rows 97 35 38 152 280 32 64 128 256), losses := [] }

theorem u14288 : Upper (D 8) (R 8) [96,33,34,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14289 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 152 336 173 205 141 397), lower := (rows 97 35 38 152 336 32 64 128 256), losses := [] }

theorem u14289 : Upper (D 8) (R 8) [96,33,34,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14290 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 200 273 188 220 156 412), lower := (rows 97 35 38 200 273 32 64 128 256), losses := [] }

theorem u14290 : Upper (D 8) (R 8) [96,33,34,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14291 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 200 276 185 217 153 409), lower := (rows 97 35 38 200 276 32 64 128 256), losses := [] }

theorem u14291 : Upper (D 8) (R 8) [96,33,34,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14292 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 200 280 181 213 149 405), lower := (rows 97 35 38 200 280 32 64 128 256), losses := [] }

theorem u14292 : Upper (D 8) (R 8) [96,33,34,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14293 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 200 400 61 93 157 285), lower := (rows 97 35 38 200 400 32 64 128 256), losses := [] }

theorem u14293 : Upper (D 8) (R 8) [96,33,34,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14294 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 74 145 436 468 404 404), lower := (rows 97 35 44 74 145 32 64 128 256), losses := [] }

theorem u14294 : Upper (D 8) (R 8) [96,33,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14295 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 74 148 433 465 401 401), lower := (rows 97 35 44 74 148 32 64 128 256), losses := [] }

theorem u14295 : Upper (D 8) (R 8) [96,33,40,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14296 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 74 273 180 212 148 404), lower := (rows 97 35 44 74 273 32 64 128 256), losses := [] }

theorem u14296 : Upper (D 8) (R 8) [96,33,40,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14297 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 74 276 177 209 145 401), lower := (rows 97 35 44 74 276 32 64 128 256), losses := [] }

theorem u14297 : Upper (D 8) (R 8) [96,33,40,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14298 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 74 400 181 213 149 405), lower := (rows 97 35 44 74 400 32 64 128 256), losses := [] }

theorem u14298 : Upper (D 8) (R 8) [96,33,40,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14299 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 88 145 422 454 390 390), lower := (rows 97 35 44 88 145 32 64 128 256), losses := [] }

theorem u14299 : Upper (D 8) (R 8) [96,33,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14300 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 88 146 421 453 389 389), lower := (rows 97 35 44 88 146 32 64 128 256), losses := [] }

theorem u14300 : Upper (D 8) (R 8) [96,33,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14301 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 88 273 166 198 134 390), lower := (rows 97 35 44 88 273 32 64 128 256), losses := [] }

theorem u14301 : Upper (D 8) (R 8) [96,33,40,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14302 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 88 274 165 197 133 389), lower := (rows 97 35 44 88 274 32 64 128 256), losses := [] }

theorem u14302 : Upper (D 8) (R 8) [96,33,40,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14303 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 88 400 167 199 135 391), lower := (rows 97 35 44 88 400 32 64 128 256), losses := [] }

theorem u14303 : Upper (D 8) (R 8) [96,33,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14304 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 137 82 436 468 404 404), lower := (rows 97 35 44 137 82 32 64 128 256), losses := [] }

theorem u14304 : Upper (D 8) (R 8) [96,33,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14305 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 137 84 434 466 402 402), lower := (rows 97 35 44 137 84 32 64 128 256), losses := [] }

theorem u14305 : Upper (D 8) (R 8) [96,33,40,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14306 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 137 146 372 340 468 340), lower := (rows 97 35 44 137 146 32 64 128 256), losses := [] }

theorem u14306 : Upper (D 8) (R 8) [96,33,40,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14307 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 137 208 310 342 406 278), lower := (rows 97 35 44 137 208 32 64 128 256), losses := [] }

theorem u14307 : Upper (D 8) (R 8) [96,33,40,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14308 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 137 274 244 212 212 468), lower := (rows 97 35 44 137 274 32 64 128 256), losses := [] }

theorem u14308 : Upper (D 8) (R 8) [96,33,40,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14309 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 137 276 242 210 210 466), lower := (rows 97 35 44 137 276 32 64 128 256), losses := [] }

theorem u14309 : Upper (D 8) (R 8) [96,33,40,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14310 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 137 336 182 214 150 406), lower := (rows 97 35 44 137 336 32 64 128 256), losses := [] }

theorem u14310 : Upper (D 8) (R 8) [96,33,40,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14311 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 137 400 118 86 214 342), lower := (rows 97 35 44 137 400 32 64 128 256), losses := [] }

theorem u14311 : Upper (D 8) (R 8) [96,33,40,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14312 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 138 84 433 465 401 401), lower := (rows 97 35 44 138 84 32 64 128 256), losses := [] }

theorem u14312 : Upper (D 8) (R 8) [96,33,40,130,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14313 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 138 145 372 340 468 340), lower := (rows 97 35 44 138 145 32 64 128 256), losses := [] }

theorem u14313 : Upper (D 8) (R 8) [96,33,40,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14314 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 138 208 309 341 405 277), lower := (rows 97 35 44 138 208 32 64 128 256), losses := [] }

theorem u14314 : Upper (D 8) (R 8) [96,33,40,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14315 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 138 273 244 212 212 468), lower := (rows 97 35 44 138 273 32 64 128 256), losses := [] }

theorem u14315 : Upper (D 8) (R 8) [96,33,40,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14316 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 138 276 241 209 209 465), lower := (rows 97 35 44 138 276 32 64 128 256), losses := [] }

theorem u14316 : Upper (D 8) (R 8) [96,33,40,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14317 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 138 336 181 213 149 405), lower := (rows 97 35 44 138 336 32 64 128 256), losses := [] }

theorem u14317 : Upper (D 8) (R 8) [96,33,40,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14318 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 138 400 117 85 213 341), lower := (rows 97 35 44 138 400 32 64 128 256), losses := [] }

theorem u14318 : Upper (D 8) (R 8) [96,33,40,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14319 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 140 82 433 465 401 401), lower := (rows 97 35 44 140 82 32 64 128 256), losses := [] }

theorem u14319 : Upper (D 8) (R 8) [96,33,40,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14320 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 140 273 242 210 210 466), lower := (rows 97 35 44 140 273 32 64 128 256), losses := [] }

theorem u14320 : Upper (D 8) (R 8) [96,33,40,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14321 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 140 274 241 209 209 465), lower := (rows 97 35 44 140 274 32 64 128 256), losses := [] }

theorem u14321 : Upper (D 8) (R 8) [96,33,40,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14322 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 140 336 179 211 147 403), lower := (rows 97 35 44 140 336 32 64 128 256), losses := [] }

theorem u14322 : Upper (D 8) (R 8) [96,33,40,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14323 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 152 82 421 453 389 389), lower := (rows 97 35 44 152 82 32 64 128 256), losses := [] }

theorem u14323 : Upper (D 8) (R 8) [96,33,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14324 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 152 273 230 198 198 454), lower := (rows 97 35 44 152 273 32 64 128 256), losses := [] }

theorem u14324 : Upper (D 8) (R 8) [96,33,40,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14325 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 152 274 229 197 197 453), lower := (rows 97 35 44 152 274 32 64 128 256), losses := [] }

theorem u14325 : Upper (D 8) (R 8) [96,33,40,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14326 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 152 276 227 195 195 451), lower := (rows 97 35 44 152 276 32 64 128 256), losses := [] }

theorem u14326 : Upper (D 8) (R 8) [96,33,40,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14327 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 152 336 167 199 135 391), lower := (rows 97 35 44 152 336 32 64 128 256), losses := [] }

theorem u14327 : Upper (D 8) (R 8) [96,33,40,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14328 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 200 145 310 342 406 278), lower := (rows 97 35 44 200 145 32 64 128 256), losses := [] }

theorem u14328 : Upper (D 8) (R 8) [96,33,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14329 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 200 146 309 341 405 277), lower := (rows 97 35 44 200 146 32 64 128 256), losses := [] }

theorem u14329 : Upper (D 8) (R 8) [96,33,40,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14330 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 200 273 182 214 150 406), lower := (rows 97 35 44 200 273 32 64 128 256), losses := [] }

theorem u14330 : Upper (D 8) (R 8) [96,33,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14331 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 200 274 181 213 149 405), lower := (rows 97 35 44 200 274 32 64 128 256), losses := [] }

theorem u14331 : Upper (D 8) (R 8) [96,33,40,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14332 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 200 276 179 211 147 403), lower := (rows 97 35 44 200 276 32 64 128 256), losses := [] }

theorem u14332 : Upper (D 8) (R 8) [96,33,40,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14333 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 200 400 55 87 151 279), lower := (rows 97 35 44 200 400 32 64 128 256), losses := [] }

theorem u14333 : Upper (D 8) (R 8) [96,33,40,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14334 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 265 82 180 212 148 404), lower := (rows 97 35 44 265 82 32 64 128 256), losses := [] }

theorem u14334 : Upper (D 8) (R 8) [96,33,40,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14335 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 265 84 178 210 146 402), lower := (rows 97 35 44 265 84 32 64 128 256), losses := [] }

theorem u14335 : Upper (D 8) (R 8) [96,33,40,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14336 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 265 146 244 212 212 468), lower := (rows 97 35 44 265 146 32 64 128 256), losses := [] }

theorem u14336 : Upper (D 8) (R 8) [96,33,40,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14337 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 265 148 242 210 210 466), lower := (rows 97 35 44 265 148 32 64 128 256), losses := [] }

theorem u14337 : Upper (D 8) (R 8) [96,33,40,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14338 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 265 208 182 214 150 406), lower := (rows 97 35 44 265 208 32 64 128 256), losses := [] }

theorem u14338 : Upper (D 8) (R 8) [96,33,40,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14339 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 266 84 177 209 145 401), lower := (rows 97 35 44 266 84 32 64 128 256), losses := [] }

theorem u14339 : Upper (D 8) (R 8) [96,33,40,258,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14339
end Delivery.IrregularNine14.P08
