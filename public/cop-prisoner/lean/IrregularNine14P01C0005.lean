import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b300 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 70 28 168 18 96 65 130 386), lower := (rows 305 70 28 168 18 96 65 128 256), losses := [] }

theorem u300 : Upper (D 1) (R 1) [304,68,24,160,2,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b300
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 28 168 18 96 66 129 385), lower := (rows 305 70 28 168 18 96 66 128 256), losses := [] }

theorem u301 : Upper (D 1) (R 1) [304,68,24,160,2,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 28 168 18 96 192 131 259), lower := (rows 305 70 28 168 18 96 192 128 256), losses := [] }

theorem u302 : Upper (D 1) (R 1) [304,68,24,160,2,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b302
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 70 28 168 80 34 65 130 386), lower := (rows 305 70 28 168 80 34 65 128 256), losses := [] }

theorem u303 : Upper (D 1) (R 1) [304,68,24,160,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b303
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 28 168 80 34 66 129 385), lower := (rows 305 70 28 168 80 34 66 128 256), losses := [] }

theorem u304 : Upper (D 1) (R 1) [304,68,24,160,64,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b304
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 28 168 80 34 192 131 259), lower := (rows 305 70 28 168 80 34 192 128 256), losses := [] }

theorem u305 : Upper (D 1) (R 1) [304,68,24,160,64,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b305
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 133 152 18 96 66 168 296), lower := (rows 305 70 133 152 18 96 66 128 256), losses := [] }

theorem u306 : Upper (D 1) (R 1) [304,68,129,144,2,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 133 152 18 96 72 162 290), lower := (rows 305 70 133 152 18 96 72 128 256), losses := [] }

theorem u307 : Upper (D 1) (R 1) [304,68,129,144,2,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b307
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 133 152 18 96 96 138 266), lower := (rows 305 70 133 152 18 96 96 128 256), losses := [] }

theorem u308 : Upper (D 1) (R 1) [304,68,129,144,2,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b308
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 133 152 80 34 66 168 296), lower := (rows 305 70 133 152 80 34 66 128 256), losses := [] }

theorem u309 : Upper (D 1) (R 1) [304,68,129,144,64,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b309
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 133 152 80 34 72 162 290), lower := (rows 305 70 133 152 80 34 72 128 256), losses := [] }

theorem u310 : Upper (D 1) (R 1) [304,68,129,144,64,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b310
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 133 152 80 34 96 138 266), lower := (rows 305 70 133 152 80 34 96 128 256), losses := [] }

theorem u311 : Upper (D 1) (R 1) [304,68,129,144,64,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b311
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 140 11 80 160 66 176 304), lower := (rows 305 70 140 11 80 160 66 128 256), losses := [] }

theorem u312 : Upper (D 1) (R 1) [304,68,136,3,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b312
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 82, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 140 11 80 160 80 162 290), lower := (rows 305 70 140 11 80 160 80 128 256), losses := [] }

theorem u313 : Upper (D 1) (R 1) [304,68,136,3,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b313
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 140 11 80 160 96 146 274), lower := (rows 305 70 140 11 80 160 96 128 256), losses := [] }

theorem u314 : Upper (D 1) (R 1) [304,68,136,3,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b314
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 305 70 148 11 18 96 72 160 416), lower := (rows 305 70 148 11 18 96 72 128 256), losses := [] }

theorem u315 : Upper (D 1) (R 1) [304,68,144,3,2,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b315
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 148, targets := 32 }], pairs := [(2,5)], upper := (rows 305 70 148 11 18 96 96 136 392), lower := (rows 305 70 148 11 18 96 96 128 256), losses := [] }

theorem u316 : Upper (D 1) (R 1) [304,68,144,3,2,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b316
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 11 18 96 192 168 296), lower := (rows 305 70 148 11 18 96 192 128 256), losses := [] }

theorem u317 : Upper (D 1) (R 1) [304,68,144,3,2,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b317
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 305 70 148 11 18 160 72 224 352), lower := (rows 305 70 148 11 18 160 72 128 256), losses := [] }

theorem u318 : Upper (D 1) (R 1) [304,68,144,3,2,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b318
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 148 11 18 160 96 200 328), lower := (rows 305 70 148 11 18 160 96 128 256), losses := [] }

theorem u319 : Upper (D 1) (R 1) [304,68,144,3,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b319
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b320 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 305 70 148 11 80 34 72 160 416), lower := (rows 305 70 148 11 80 34 72 128 256), losses := [] }

theorem u320 : Upper (D 1) (R 1) [304,68,144,3,64,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b320
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b321 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 148 11 80 34 96 136 392), lower := (rows 305 70 148 11 80 34 96 128 256), losses := [] }

theorem u321 : Upper (D 1) (R 1) [304,68,144,3,64,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b321
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b322 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 11 80 34 192 168 296), lower := (rows 305 70 148 11 80 34 192 128 256), losses := [] }

theorem u322 : Upper (D 1) (R 1) [304,68,144,3,64,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b322
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 148 11 80 160 66 168 296), lower := (rows 305 70 148 11 80 160 66 128 256), losses := [] }

theorem u323 : Upper (D 1) (R 1) [304,68,144,3,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b323
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 148 11 80 160 72 162 290), lower := (rows 305 70 148 11 80 160 72 128 256), losses := [] }

theorem u324 : Upper (D 1) (R 1) [304,68,144,3,64,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b324
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 148 11 80 160 96 138 266), lower := (rows 305 70 148 11 80 160 96 128 256), losses := [] }

theorem u325 : Upper (D 1) (R 1) [304,68,144,3,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b325
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 148 73 18 160 66 168 296), lower := (rows 305 70 148 73 18 160 66 128 256), losses := [] }

theorem u326 : Upper (D 1) (R 1) [304,68,144,65,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b326
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b327 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 148 73 18 160 72 162 290), lower := (rows 305 70 148 73 18 160 72 128 256), losses := [] }

theorem u327 : Upper (D 1) (R 1) [304,68,144,65,2,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b327
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b328 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 305 70 148 73 18 160 96 138 266), lower := (rows 305 70 148 73 18 160 96 128 256), losses := [] }

theorem u328 : Upper (D 1) (R 1) [304,68,144,65,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b328
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b329 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 148 137 18 96 66 168 296), lower := (rows 305 70 148 137 18 96 66 128 256), losses := [] }

theorem u329 : Upper (D 1) (R 1) [304,68,144,129,2,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b329
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b330 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 148 137 18 96 72 162 290), lower := (rows 305 70 148 137 18 96 72 128 256), losses := [] }

theorem u330 : Upper (D 1) (R 1) [304,68,144,129,2,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b330
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b331 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 148 137 18 96 96 138 266), lower := (rows 305 70 148 137 18 96 96 128 256), losses := [] }

theorem u331 : Upper (D 1) (R 1) [304,68,144,129,2,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 148 137 80 34 66 168 296), lower := (rows 305 70 148 137 80 34 66 128 256), losses := [] }

theorem u332 : Upper (D 1) (R 1) [304,68,144,129,64,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b332
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 148 137 80 34 72 162 290), lower := (rows 305 70 148 137 80 34 72 128 256), losses := [] }

theorem u333 : Upper (D 1) (R 1) [304,68,144,129,64,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b333
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 148 137 80 34 96 138 266), lower := (rows 305 70 148 137 80 34 96 128 256), losses := [] }

theorem u334 : Upper (D 1) (R 1) [304,68,144,129,64,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b334
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 70 148 168 18 96 65 138 266), lower := (rows 305 70 148 168 18 96 65 128 256), losses := [] }

theorem u335 : Upper (D 1) (R 1) [304,68,144,160,2,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b335
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 148 168 18 96 66 137 265), lower := (rows 305 70 148 168 18 96 66 128 256), losses := [] }

theorem u336 : Upper (D 1) (R 1) [304,68,144,160,2,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b336
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 70 148 168 18 96 72 131 259), lower := (rows 305 70 148 168 18 96 72 128 256), losses := [] }

theorem u337 : Upper (D 1) (R 1) [304,68,144,160,2,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b337
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 70 148 168 80 34 65 138 266), lower := (rows 305 70 148 168 80 34 65 128 256), losses := [] }

theorem u338 : Upper (D 1) (R 1) [304,68,144,160,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b338
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 148 168 80 34 66 137 265), lower := (rows 305 70 148 168 80 34 66 128 256), losses := [] }

theorem u339 : Upper (D 1) (R 1) [304,68,144,160,64,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b339
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 70 148 168 80 34 72 131 259), lower := (rows 305 70 148 168 80 34 72 128 256), losses := [] }

theorem u340 : Upper (D 1) (R 1) [304,68,144,160,64,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b340
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 14 144 96 66 160 416), lower := (rows 305 82 13 14 144 96 66 128 256), losses := [] }

theorem u341 : Upper (D 1) (R 1) [304,80,9,6,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b341
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 305 82 13 14 144 96 96 130 386), lower := (rows 305 82 13 14 144 96 96 128 256), losses := [] }

theorem u342 : Upper (D 1) (R 1) [304,80,9,6,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b342
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 305 82 13 14 144 96 192 162 290), lower := (rows 305 82 13 14 144 96 192 128 256), losses := [] }

theorem u343 : Upper (D 1) (R 1) [304,80,9,6,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b343
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 305 82 13 138 144 34 68 224 352), lower := (rows 305 82 13 138 144 34 68 128 256), losses := [] }

theorem u344 : Upper (D 1) (R 1) [304,80,9,130,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b344
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 305 82 13 138 144 34 96 196 324), lower := (rows 305 82 13 138 144 34 96 128 256), losses := [] }

theorem u345 : Upper (D 1) (R 1) [304,80,9,130,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 138 144 96 66 164 292), lower := (rows 305 82 13 138 144 96 66 128 256), losses := [] }

theorem u346 : Upper (D 1) (R 1) [304,80,9,130,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b346
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 82 13 138 144 96 68 162 290), lower := (rows 305 82 13 138 144 96 68 128 256), losses := [] }

theorem u347 : Upper (D 1) (R 1) [304,80,9,130,128,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b347
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 305 82 13 138 144 96 96 134 262), lower := (rows 305 82 13 138 144 96 96 128 256), losses := [] }

theorem u348 : Upper (D 1) (R 1) [304,80,9,130,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b348
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 305 82 14 137 144 34 68 224 352), lower := (rows 305 82 14 137 144 34 68 128 256), losses := [] }

theorem u349 : Upper (D 1) (R 1) [304,80,10,129,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b349
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 305 82 14 137 144 34 96 196 324), lower := (rows 305 82 14 137 144 34 96 128 256), losses := [] }

theorem u350 : Upper (D 1) (R 1) [304,80,10,129,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b350
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 14 137 144 96 66 164 292), lower := (rows 305 82 14 137 144 96 66 128 256), losses := [] }

theorem u351 : Upper (D 1) (R 1) [304,80,10,129,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b351
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 82 14 137 144 96 68 162 290), lower := (rows 305 82 14 137 144 96 68 128 256), losses := [] }

theorem u352 : Upper (D 1) (R 1) [304,80,10,129,128,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b352
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 305 82 14 137 144 96 96 134 262), lower := (rows 305 82 14 137 144 96 96 128 256), losses := [] }

theorem u353 : Upper (D 1) (R 1) [304,80,10,129,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b353
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 68, camps := [], pairs := [], upper := (rows 305 82 14 168 144 34 65 196 324), lower := (rows 305 82 14 168 144 34 65 128 256), losses := [] }

theorem u354 : Upper (D 1) (R 1) [304,80,10,160,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b354
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 305 82 14 168 144 34 68 193 321), lower := (rows 305 82 14 168 144 34 68 128 256), losses := [] }

theorem u355 : Upper (D 1) (R 1) [304,80,10,160,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b355
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 82 14 168 144 96 65 134 262), lower := (rows 305 82 14 168 144 96 65 128 256), losses := [] }

theorem u356 : Upper (D 1) (R 1) [304,80,10,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b356
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 14 168 144 96 66 133 261), lower := (rows 305 82 14 168 144 96 66 128 256), losses := [] }

theorem u357 : Upper (D 1) (R 1) [304,80,10,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b357
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 82 14 168 144 96 68 131 259), lower := (rows 305 82 14 168 144 96 68 128 256), losses := [] }

theorem u358 : Upper (D 1) (R 1) [304,80,10,160,128,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b358
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 305 82 69 138 144 34 68 168 296), lower := (rows 305 82 69 138 144 34 68 128 256), losses := [] }

theorem u359 : Upper (D 1) (R 1) [304,80,65,130,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b359
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P01
