import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b300 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 259 7 44 200 81 33 80 160 416), lower := (rows 259 7 44 200 81 33 80 128 256), losses := [] }

theorem u300 : Upper (D 3) (R 3) [258,5,40,192,65,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b300
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 136, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 44 200 81 33 96 144 400), lower := (rows 259 7 44 200 81 33 96 128 256), losses := [] }

theorem u301 : Upper (D 3) (R 3) [258,5,40,192,65,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b301
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 44 200 81 33 192 176 304), lower := (rows 259 7 44 200 81 33 192 128 256), losses := [] }

theorem u302 : Upper (D 3) (R 3) [258,5,40,192,65,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b302
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 140, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 200 112 33 65 144 400), lower := (rows 259 7 44 200 112 33 65 128 256), losses := [] }

theorem u303 : Upper (D 3) (R 3) [258,5,40,192,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b303
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 7 44 200 112 33 80 129 385), lower := (rows 259 7 44 200 112 33 80 128 256), losses := [] }

theorem u304 : Upper (D 3) (R 3) [258,5,40,192,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b304
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 44 200 112 33 192 145 273), lower := (rows 259 7 44 200 112 33 192 128 256), losses := [] }

theorem u305 : Upper (D 3) (R 3) [258,5,40,192,96,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b305
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 192, camps := [], pairs := [], upper := (rows 259 7 100 25 176 33 72 192 448), lower := (rows 259 7 100 25 176 33 72 128 256), losses := [] }

theorem u306 : Upper (D 3) (R 3) [258,5,96,17,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b306
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 25 176 33 192 200 328), lower := (rows 259 7 100 25 176 33 192 128 256), losses := [] }

theorem u307 : Upper (D 3) (R 3) [258,5,96,17,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b307
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 56 208 33 65 136 392), lower := (rows 259 7 100 56 208 33 65 128 256), losses := [] }

theorem u308 : Upper (D 3) (R 3) [258,5,96,48,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b308
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 7 100 56 208 33 72 129 385), lower := (rows 259 7 100 56 208 33 72 128 256), losses := [] }

theorem u309 : Upper (D 3) (R 3) [258,5,96,48,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b309
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 56 208 33 192 137 265), lower := (rows 259 7 100 56 208 33 192 128 256), losses := [] }

theorem u310 : Upper (D 3) (R 3) [258,5,96,48,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b310
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 168 208 33 65 152 280), lower := (rows 259 7 100 168 208 33 65 128 256), losses := [] }

theorem u311 : Upper (D 3) (R 3) [258,5,96,160,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b311
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 7 100 168 208 33 72 145 273), lower := (rows 259 7 100 168 208 33 72 128 256), losses := [] }

theorem u312 : Upper (D 3) (R 3) [258,5,96,160,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b312
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 259 7 100 168 208 33 80 137 265), lower := (rows 259 7 100 168 208 33 80 128 256), losses := [] }

theorem u313 : Upper (D 3) (R 3) [258,5,96,160,192,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b313
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 38, targets := 128 }], pairs := [(1,7)], upper := (rows 259 14 37 73 112 33 192 144 400), lower := (rows 259 14 37 73 112 33 192 128 256), losses := [] }

theorem u314 : Upper (D 3) (R 3) [258,12,33,65,96,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b314
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 14 37 73 112 48 192 129 385), lower := (rows 259 14 37 73 112 48 192 128 256), losses := [] }

theorem u315 : Upper (D 3) (R 3) [258,12,33,65,96,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b315
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 259 14 37 73 112 160 192 145 273), lower := (rows 259 14 37 73 112 160 192 128 256), losses := [] }

theorem u316 : Upper (D 3) (R 3) [258,12,33,65,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b316
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 259 35 44 73 148 160 65 208 336), lower := (rows 259 35 44 73 148 160 65 128 256), losses := [] }

theorem u317 : Upper (D 3) (R 3) [258,33,40,65,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b317
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 259 35 44 73 148 160 80 193 321), lower := (rows 259 35 44 73 148 160 80 128 256), losses := [] }

theorem u318 : Upper (D 3) (R 3) [258,33,40,65,132,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b318
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 259 35 44 73 208 160 65 148 276), lower := (rows 259 35 44 73 208 160 65 128 256), losses := [] }

theorem u319 : Upper (D 3) (R 3) [258,33,40,65,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b319
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b320 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 35 44 73 208 160 68 145 273), lower := (rows 259 35 44 73 208 160 68 128 256), losses := [] }

theorem u320 : Upper (D 3) (R 3) [258,33,40,65,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b320
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b321 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 259 35 44 73 208 160 80 133 261), lower := (rows 259 35 44 73 208 160 80 128 256), losses := [] }

theorem u321 : Upper (D 3) (R 3) [258,33,40,65,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b321
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b322 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 69 104 148 160 65 152 280), lower := (rows 259 35 69 104 148 160 65 128 256), losses := [] }

theorem u322 : Upper (D 3) (R 3) [258,33,65,96,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b322
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 35 69 104 148 160 72 145 273), lower := (rows 259 35 69 104 148 160 72 128 256), losses := [] }

theorem u323 : Upper (D 3) (R 3) [258,33,65,96,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b323
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 259 35 69 104 148 160 80 137 265), lower := (rows 259 35 69 104 148 160 80 128 256), losses := [] }

theorem u324 : Upper (D 3) (R 3) [258,33,65,96,132,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b324
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 69 104 152 160 65 148 276), lower := (rows 259 35 69 104 152 160 65 128 256), losses := [] }

theorem u325 : Upper (D 3) (R 3) [258,33,65,96,136,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b325
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 35 69 104 152 160 68 145 273), lower := (rows 259 35 69 104 152 160 68 128 256), losses := [] }

theorem u326 : Upper (D 3) (R 3) [258,33,65,96,136,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b326
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b327 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 259 35 69 104 152 160 80 133 261), lower := (rows 259 35 69 104 152 160 80 128 256), losses := [] }

theorem u327 : Upper (D 3) (R 3) [258,33,65,96,136,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b327
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b328 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 25 208 160 65 168 296), lower := (rows 259 38 69 25 208 160 65 128 256), losses := [] }

theorem u328 : Upper (D 3) (R 3) [258,36,65,17,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b328
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b329 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 69 25 208 160 72 161 289), lower := (rows 259 38 69 25 208 160 72 128 256), losses := [] }

theorem u329 : Upper (D 3) (R 3) [258,36,65,17,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b329
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b330 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 25 208 160 96 137 265), lower := (rows 259 38 69 25 208 160 96 128 256), losses := [] }

theorem u330 : Upper (D 3) (R 3) [258,36,65,17,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b330
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b331 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 88 145 160 65 168 296), lower := (rows 259 38 69 88 145 160 65 128 256), losses := [] }

theorem u331 : Upper (D 3) (R 3) [258,36,65,80,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b331
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 69 88 145 160 72 161 289), lower := (rows 259 38 69 88 145 160 72 128 256), losses := [] }

theorem u332 : Upper (D 3) (R 3) [258,36,65,80,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b332
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 88 145 160 96 137 265), lower := (rows 259 38 69 88 145 160 96 128 256), losses := [] }

theorem u333 : Upper (D 3) (R 3) [258,36,65,80,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b333
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 104 145 160 65 152 280), lower := (rows 259 38 69 104 145 160 65 128 256), losses := [] }

theorem u334 : Upper (D 3) (R 3) [258,36,65,96,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b334
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 38 69 104 145 160 72 145 273), lower := (rows 259 38 69 104 145 160 72 128 256), losses := [] }

theorem u335 : Upper (D 3) (R 3) [258,36,65,96,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b335
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 259 38 69 104 145 160 80 137 265), lower := (rows 259 38 69 104 145 160 80 128 256), losses := [] }

theorem u336 : Upper (D 3) (R 3) [258,36,65,96,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b336
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 104 152 160 65 145 273), lower := (rows 259 38 69 104 152 160 65 128 256), losses := [] }

theorem u337 : Upper (D 3) (R 3) [258,36,65,96,136,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b337
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 259 38 69 104 152 160 80 129 257), lower := (rows 259 38 69 104 152 160 80 128 256), losses := [] }

theorem u338 : Upper (D 3) (R 3) [258,36,65,96,136,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b338
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 9, camps := [], pairs := [(2,5)], upper := (rows 259 38 196 88 176 33 65 137 265), lower := (rows 259 38 196 88 176 33 65 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 97 128 256), good := (rows 323 70 196 92 220 65 65 128 256) }] }

theorem u339 : Upper (D 3) (R 3) [258,36,192,80,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b339
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 259 38 196 88 176 33 72 129 257), lower := (rows 259 38 196 88 176 33 72 128 256), losses := [] }

theorem u340 : Upper (D 3) (R 3) [258,36,192,80,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b340
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 200 145 33 65 148 276), lower := (rows 259 98 44 200 145 33 65 128 256), losses := [] }

theorem u341 : Upper (D 3) (R 3) [258,96,40,192,129,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b341
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 98 44 200 145 33 68 145 273), lower := (rows 259 98 44 200 145 33 68 128 256), losses := [] }

theorem u342 : Upper (D 3) (R 3) [258,96,40,192,129,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b342
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 259 98 44 200 145 33 80 133 261), lower := (rows 259 98 44 200 145 33 80 128 256), losses := [] }

theorem u343 : Upper (D 3) (R 3) [258,96,40,192,129,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b343
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 289 7 28 73 145 96 66 160 416), lower := (rows 289 7 28 73 145 96 66 128 256), losses := [] }

theorem u344 : Upper (D 3) (R 3) [288,5,24,65,129,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b344
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 28 73 145 96 96 130 386), lower := (rows 289 7 28 73 145 96 96 128 256), losses := [] }

theorem u345 : Upper (D 3) (R 3) [288,5,24,65,129,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b345
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 28 73 145 96 192 162 290), lower := (rows 289 7 28 73 145 96 192 128 256), losses := [] }

theorem u346 : Upper (D 3) (R 3) [288,5,24,65,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b346
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 289 7 76 137 81 160 66 176 304), lower := (rows 289 7 76 137 81 160 66 128 256), losses := [] }

theorem u347 : Upper (D 3) (R 3) [288,5,72,129,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b347
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 289 7 76 137 81 160 80 162 290), lower := (rows 289 7 76 137 81 160 80 128 256), losses := [] }

theorem u348 : Upper (D 3) (R 3) [288,5,72,129,65,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b348
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 137 81 160 96 146 274), lower := (rows 289 7 76 137 81 160 96 128 256), losses := [] }

theorem u349 : Upper (D 3) (R 3) [288,5,72,129,65,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b349
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 137 176 96 65 146 274), lower := (rows 289 7 76 137 176 96 65 128 256), losses := [] }

theorem u350 : Upper (D 3) (R 3) [288,5,72,129,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b350
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 7 76 137 176 96 66 145 273), lower := (rows 289 7 76 137 176 96 66 128 256), losses := [] }

theorem u351 : Upper (D 3) (R 3) [288,5,72,129,160,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b351
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 7 76 137 176 96 80 131 259), lower := (rows 289 7 76 137 176 96 80 128 256), losses := [] }

theorem u352 : Upper (D 3) (R 3) [288,5,72,129,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b352
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 88, targets := 128 }], pairs := [(3,7)], upper := (rows 289 7 196 56 81 160 65 138 266), lower := (rows 289 7 196 56 81 160 65 128 256), losses := [] }

theorem u353 : Upper (D 3) (R 3) [288,5,192,48,65,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b353
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 289 7 196 56 81 160 66 137 265), lower := (rows 289 7 196 56 81 160 66 128 256), losses := [] }

theorem u354 : Upper (D 3) (R 3) [288,5,192,48,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b354
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 7 196 56 81 160 72 131 259), lower := (rows 289 7 196 56 81 160 72 128 256), losses := [] }

theorem u355 : Upper (D 3) (R 3) [288,5,192,48,65,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b355
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 110, targets := 128 }], pairs := [(1,7)], upper := (rows 289 14 52 73 145 96 65 130 386), lower := (rows 289 14 52 73 145 96 65 128 256), losses := [] }

theorem u356 : Upper (D 3) (R 3) [288,12,48,65,129,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b356
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 289 14 52 73 145 96 66 129 385), lower := (rows 289 14 52 73 145 96 66 128 256), losses := [] }

theorem u357 : Upper (D 3) (R 3) [288,12,48,65,129,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b357
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 289 14 52 73 145 96 192 131 259), lower := (rows 289 14 52 73 145 96 192 128 256), losses := [] }

theorem u358 : Upper (D 3) (R 3) [288,12,48,65,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b358
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 137 112 160 65 146 274), lower := (rows 289 14 69 137 112 160 65 128 256), losses := [] }

theorem u359 : Upper (D 3) (R 3) [288,12,65,129,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b359
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P03
