import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b300 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 26 76 137 304 36 96 131 259), lower := (rows 7 26 76 137 304 36 96 128 256), losses := [] }

theorem u300 : Upper (D 5) (R 5) [6,24,72,129,288,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b300
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 76 168 273 33 66 164 292), lower := (rows 7 26 76 168 273 33 66 128 256), losses := [] }

theorem u301 : Upper (D 5) (R 5) [6,24,72,160,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b301
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 76 168 273 33 68 162 290), lower := (rows 7 26 76 168 273 33 68 128 256), losses := [] }

theorem u302 : Upper (D 5) (R 5) [6,24,72,160,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b302
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 275, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 168 273 33 96 134 262), lower := (rows 7 26 76 168 273 33 96 128 256), losses := [] }

theorem u303 : Upper (D 5) (R 5) [6,24,72,160,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b303
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 168 273 34 65 164 292), lower := (rows 7 26 76 168 273 34 65 128 256), losses := [] }

theorem u304 : Upper (D 5) (R 5) [6,24,72,160,257,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b304
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 76 168 273 34 68 161 289), lower := (rows 7 26 76 168 273 34 68 128 256), losses := [] }

theorem u305 : Upper (D 5) (R 5) [6,24,72,160,257,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b305
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 275, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 76 168 273 34 96 133 261), lower := (rows 7 26 76 168 273 34 96 128 256), losses := [] }

theorem u306 : Upper (D 5) (R 5) [6,24,72,160,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b306
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 76 168 273 36 65 162 290), lower := (rows 7 26 76 168 273 36 65 128 256), losses := [] }

theorem u307 : Upper (D 5) (R 5) [6,24,72,160,257,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b307
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 76 168 273 36 66 161 289), lower := (rows 7 26 76 168 273 36 66 128 256), losses := [] }

theorem u308 : Upper (D 5) (R 5) [6,24,72,160,257,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b308
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 76 168 273 36 96 131 259), lower := (rows 7 26 76 168 273 36 96 128 256), losses := [] }

theorem u309 : Upper (D 5) (R 5) [6,24,72,160,257,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b309
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 100 42 145 288 65 140 268), lower := (rows 7 26 100 42 145 288 65 128 256), losses := [] }

theorem u310 : Upper (D 5) (R 5) [6,24,96,34,129,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b310
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 26 100 42 145 288 68 137 265), lower := (rows 7 26 100 42 145 288 68 128 256), losses := [] }

theorem u311 : Upper (D 5) (R 5) [6,24,96,34,129,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b311
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 144, targets := 2 }], pairs := [(4,1)], upper := (rows 7 26 100 42 145 288 72 133 261), lower := (rows 7 26 100 42 145 288 72 128 256), losses := [] }

theorem u312 : Upper (D 5) (R 5) [6,24,96,34,129,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b312
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 100 42 148 33 65 392 264), lower := (rows 7 26 100 42 148 33 65 128 256), losses := [] }

theorem u313 : Upper (D 5) (R 5) [6,24,96,34,132,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b313
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 400, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 42 148 33 72 385 257), lower := (rows 7 26 100 42 148 33 72 128 256), losses := [] }

theorem u314 : Upper (D 5) (R 5) [6,24,96,34,132,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b314
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 40, targets := 4 }], pairs := [(3,2)], upper := (rows 7 26 100 42 148 33 320 137 265), lower := (rows 7 26 100 42 148 33 320 128 256), losses := [] }

theorem u315 : Upper (D 5) (R 5) [6,24,96,34,132,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b315
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 100 42 400 33 65 140 268), lower := (rows 7 26 100 42 400 33 65 128 256), losses := [] }

theorem u316 : Upper (D 5) (R 5) [6,24,96,34,384,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b316
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 100 42 400 33 68 137 265), lower := (rows 7 26 100 42 400 33 68 128 256), losses := [] }

theorem u317 : Upper (D 5) (R 5) [6,24,96,34,384,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b317
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 400, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 42 400 33 72 133 261), lower := (rows 7 26 100 42 400 33 72 128 256), losses := [] }

theorem u318 : Upper (D 5) (R 5) [6,24,96,34,384,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b318
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 100 137 273 34 68 168 296), lower := (rows 7 26 100 137 273 34 68 128 256), losses := [] }

theorem u319 : Upper (D 5) (R 5) [6,24,96,129,257,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b319
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b320 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 1, region := 100, targets := 1 }], pairs := [(2,0),(4,3)], upper := (rows 7 26 100 137 273 34 72 164 292), lower := (rows 7 26 100 137 273 34 72 128 256), losses := [] }

theorem u320 : Upper (D 5) (R 5) [6,24,96,129,257,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b320
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b321 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 137 273 34 96 140 268), lower := (rows 7 26 100 137 273 34 96 128 256), losses := [] }

theorem u321 : Upper (D 5) (R 5) [6,24,96,129,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b321
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b322 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 100 137 273 40 66 164 292), lower := (rows 7 26 100 137 273 40 66 128 256), losses := [] }

theorem u322 : Upper (D 5) (R 5) [6,24,96,129,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b322
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 100 137 273 40 68 162 290), lower := (rows 7 26 100 137 273 40 68 128 256), losses := [] }

theorem u323 : Upper (D 5) (R 5) [6,24,96,129,257,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b323
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 137 273 40 96 134 262), lower := (rows 7 26 100 137 273 40 96 128 256), losses := [] }

theorem u324 : Upper (D 5) (R 5) [6,24,96,129,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b324
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 100 137 276 33 66 168 296), lower := (rows 7 26 100 137 276 33 66 128 256), losses := [] }

theorem u325 : Upper (D 5) (R 5) [6,24,96,129,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b325
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 168, targets := 4 },{ cop := 0, region := 304, targets := 8 }], pairs := [(3,2),(4,3)], upper := (rows 7 26 100 137 276 33 72 162 290), lower := (rows 7 26 100 137 276 33 72 128 256), losses := [] }

theorem u326 : Upper (D 5) (R 5) [6,24,96,129,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b326
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b327 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 137 276 33 96 138 266), lower := (rows 7 26 100 137 276 33 96 128 256), losses := [] }

theorem u327 : Upper (D 5) (R 5) [6,24,96,129,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b327
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b328 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 100 137 276 34 65 168 296), lower := (rows 7 26 100 137 276 34 65 128 256), losses := [] }

theorem u328 : Upper (D 5) (R 5) [6,24,96,129,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b328
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b329 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 4 },{ cop := 0, region := 304, targets := 8 }], pairs := [(3,2),(4,3)], upper := (rows 7 26 100 137 276 34 72 161 289), lower := (rows 7 26 100 137 276 34 72 128 256), losses := [] }

theorem u329 : Upper (D 5) (R 5) [6,24,96,129,260,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b329
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b330 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 137 276 34 96 137 265), lower := (rows 7 26 100 137 276 34 96 128 256), losses := [] }

theorem u330 : Upper (D 5) (R 5) [6,24,96,129,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b330
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b331 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 168, targets := 4 },{ cop := 3, region := 100, targets := 2 }], pairs := [(2,1),(3,2)], upper := (rows 7 26 100 137 276 40 65 162 290), lower := (rows 7 26 100 137 276 40 65 128 256), losses := [] }

theorem u331 : Upper (D 5) (R 5) [6,24,96,129,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b331
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 100 137 276 40 66 161 289), lower := (rows 7 26 100 137 276 40 66 128 256), losses := [] }

theorem u332 : Upper (D 5) (R 5) [6,24,96,129,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b332
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 137 276 40 96 131 259), lower := (rows 7 26 100 137 276 40 96 128 256), losses := [] }

theorem u333 : Upper (D 5) (R 5) [6,24,96,129,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b333
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 136, targets := 32 },{ cop := 3, region := 100, targets := 2 }], pairs := [(2,1),(3,5)], upper := (rows 7 26 100 137 304 40 65 134 262), lower := (rows 7 26 100 137 304 40 65 128 256), losses := [] }

theorem u334 : Upper (D 5) (R 5) [6,24,96,129,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b334
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 100 137 304 40 66 133 261), lower := (rows 7 26 100 137 304 40 66 128 256), losses := [] }

theorem u335 : Upper (D 5) (R 5) [6,24,96,129,288,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b335
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 100 137 304 40 68 131 259), lower := (rows 7 26 100 137 304 40 68 128 256), losses := [] }

theorem u336 : Upper (D 5) (R 5) [6,24,96,129,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b336
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 100 138 276 33 65 168 296), lower := (rows 7 26 100 138 276 33 65 128 256), losses := [] }

theorem u337 : Upper (D 5) (R 5) [6,24,96,130,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b337
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 138 276 33 72 161 289), lower := (rows 7 26 100 138 276 33 72 128 256), losses := [] }

theorem u338 : Upper (D 5) (R 5) [6,24,96,130,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b338
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 138 276 33 96 137 265), lower := (rows 7 26 100 138 276 33 96 128 256), losses := [] }

theorem u339 : Upper (D 5) (R 5) [6,24,96,130,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b339
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 100 138 304 33 65 140 268), lower := (rows 7 26 100 138 304 33 65 128 256), losses := [] }

theorem u340 : Upper (D 5) (R 5) [6,24,96,130,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b340
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 100 138 304 33 68 137 265), lower := (rows 7 26 100 138 304 33 68 128 256), losses := [] }

theorem u341 : Upper (D 5) (R 5) [6,24,96,130,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b341
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 138 304 33 72 133 261), lower := (rows 7 26 100 138 304 33 72 128 256), losses := [] }

theorem u342 : Upper (D 5) (R 5) [6,24,96,130,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b342
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 100 140 273 33 66 168 296), lower := (rows 7 26 100 140 273 33 66 128 256), losses := [] }

theorem u343 : Upper (D 5) (R 5) [6,24,96,132,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b343
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 100 140 273 33 72 162 290), lower := (rows 7 26 100 140 273 33 72 128 256), losses := [] }

theorem u344 : Upper (D 5) (R 5) [6,24,96,132,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b344
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 140 273 33 96 138 266), lower := (rows 7 26 100 140 273 33 96 128 256), losses := [] }

theorem u345 : Upper (D 5) (R 5) [6,24,96,132,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b345
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 100 140 273 34 65 168 296), lower := (rows 7 26 100 140 273 34 65 128 256), losses := [] }

theorem u346 : Upper (D 5) (R 5) [6,24,96,132,257,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b346
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 100 140 273 34 72 161 289), lower := (rows 7 26 100 140 273 34 72 128 256), losses := [] }

theorem u347 : Upper (D 5) (R 5) [6,24,96,132,257,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b347
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 140 273 34 96 137 265), lower := (rows 7 26 100 140 273 34 96 128 256), losses := [] }

theorem u348 : Upper (D 5) (R 5) [6,24,96,132,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b348
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 100 140 273 40 65 162 290), lower := (rows 7 26 100 140 273 40 65 128 256), losses := [{ target := 0, region := (rows 0 18 68 73 16 127 64 147 275), good := (rows 430 442 108 172 442 40 492 128 256) }] }

theorem u349 : Upper (D 5) (R 5) [6,24,96,132,257,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b349
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 100 140 273 40 66 161 289), lower := (rows 7 26 100 140 273 40 66 128 256), losses := [] }

theorem u350 : Upper (D 5) (R 5) [6,24,96,132,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b350
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 140 273 40 96 131 259), lower := (rows 7 26 100 140 273 40 96 128 256), losses := [] }

theorem u351 : Upper (D 5) (R 5) [6,24,96,132,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b351
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 100 140 304 33 65 138 266), lower := (rows 7 26 100 140 304 33 65 128 256), losses := [] }

theorem u352 : Upper (D 5) (R 5) [6,24,96,132,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b352
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 100 140 304 33 66 137 265), lower := (rows 7 26 100 140 304 33 66 128 256), losses := [] }

theorem u353 : Upper (D 5) (R 5) [6,24,96,132,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b353
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 100 140 304 33 72 131 259), lower := (rows 7 26 100 140 304 33 72 128 256), losses := [] }

theorem u354 : Upper (D 5) (R 5) [6,24,96,132,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b354
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 100 168 273 33 66 140 268), lower := (rows 7 26 100 168 273 33 66 128 256), losses := [] }

theorem u355 : Upper (D 5) (R 5) [6,24,96,160,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b355
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 100 168 273 33 68 138 266), lower := (rows 7 26 100 168 273 33 68 128 256), losses := [] }

theorem u356 : Upper (D 5) (R 5) [6,24,96,160,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b356
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 168 273 33 72 134 262), lower := (rows 7 26 100 168 273 33 72 128 256), losses := [] }

theorem u357 : Upper (D 5) (R 5) [6,24,96,160,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b357
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 100 168 273 34 65 140 268), lower := (rows 7 26 100 168 273 34 65 128 256), losses := [] }

theorem u358 : Upper (D 5) (R 5) [6,24,96,160,257,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b358
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 100 168 273 34 68 137 265), lower := (rows 7 26 100 168 273 34 68 128 256), losses := [] }

theorem u359 : Upper (D 5) (R 5) [6,24,96,160,257,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b359
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P05
