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

def b300 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 44 73 112 160 192 145 273), lower := (rows 35 262 44 73 112 160 192 128 256), losses := [] }

theorem u300 : Upper (D 8) (R 8) [34,260,40,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 262 44 73 145 160 80 224 352), lower := (rows 35 262 44 73 145 160 80 128 256), losses := [] }

theorem u301 : Upper (D 8) (R 8) [34,260,40,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b301 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7)], upper := (rows 35 262 44 73 145 160 96 208 336), lower := (rows 35 262 44 73 145 160 96 128 256), losses := [] }

theorem u302 : Upper (D 8) (R 8) [34,260,40,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0)], upper := (rows 35 262 44 73 208 160 65 176 304), lower := (rows 35 262 44 73 208 160 65 128 256), losses := [] }

theorem u303 : Upper (D 8) (R 8) [34,260,40,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 262 44 73 208 160 80 161 289), lower := (rows 35 262 44 73 208 160 80 128 256), losses := [] }

theorem u304 : Upper (D 8) (R 8) [34,260,40,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b304 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7)], upper := (rows 35 262 44 73 208 160 96 145 273), lower := (rows 35 262 44 73 208 160 96 128 256), losses := [] }

theorem u305 : Upper (D 8) (R 8) [34,260,40,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0)], upper := (rows 35 262 69 104 152 160 65 176 304), lower := (rows 35 262 69 104 152 160 65 128 256), losses := [] }

theorem u306 : Upper (D 8) (R 8) [34,260,65,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 262 69 104 152 160 80 161 289), lower := (rows 35 262 69 104 152 160 80 128 256), losses := [] }

theorem u307 : Upper (D 8) (R 8) [34,260,65,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b307 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 35 262 69 104 152 160 96 145 273), lower := (rows 35 262 69 104 152 160 96 128 256), losses := [] }

theorem u308 : Upper (D 8) (R 8) [34,260,65,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 322 13 152 112 160 65 164 292), lower := (rows 35 322 13 152 112 160 65 128 256), losses := [] }

theorem u309 : Upper (D 8) (R 8) [34,320,9,144,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 322 13 152 112 160 68 161 289), lower := (rows 35 322 13 152 112 160 68 128 256), losses := [] }

theorem u310 : Upper (D 8) (R 8) [34,320,9,144,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b310 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 35 322 13 152 112 160 96 133 261), lower := (rows 35 322 13 152 112 160 96 128 256), losses := [] }

theorem u311 : Upper (D 8) (R 8) [34,320,9,144,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 35 322 28 104 145 160 65 164 292), lower := (rows 35 322 28 104 145 160 65 128 256), losses := [] }

theorem u312 : Upper (D 8) (R 8) [34,320,24,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 322 28 104 145 160 68 161 289), lower := (rows 35 322 28 104 145 160 68 128 256), losses := [] }

theorem u313 : Upper (D 8) (R 8) [34,320,24,96,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b313 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 104 145 160 96 133 261), lower := (rows 35 322 28 104 145 160 96 128 256), losses := [] }

theorem u314 : Upper (D 8) (R 8) [34,320,24,96,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 168 304 96 65 160 416), lower := (rows 67 7 28 168 304 96 65 128 256), losses := [] }

theorem u315 : Upper (D 8) (R 8) [66,5,24,160,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 28 168 304 96 96 129 385), lower := (rows 67 7 28 168 304 96 96 128 256), losses := [] }

theorem u316 : Upper (D 8) (R 8) [66,5,24,160,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 128 }], pairs := [(4,7)], upper := (rows 67 7 28 168 304 96 192 161 289), lower := (rows 67 7 28 168 304 96 192 128 256), losses := [] }

theorem u317 : Upper (D 8) (R 8) [66,5,24,160,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 152 304 96 65 160 416), lower := (rows 67 7 44 152 304 96 65 128 256), losses := [] }

theorem u318 : Upper (D 8) (R 8) [66,5,40,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 152 304 96 96 129 385), lower := (rows 67 7 44 152 304 96 96 128 256), losses := [] }

theorem u319 : Upper (D 8) (R 8) [66,5,40,144,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b320 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 128 }], pairs := [(4,7)], upper := (rows 67 7 44 152 304 96 192 161 289), lower := (rows 67 7 44 152 304 96 192 128 256), losses := [] }

theorem u320 : Upper (D 8) (R 8) [66,5,40,144,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b321 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 396, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 280 112 160 65 160 416), lower := (rows 67 7 44 280 112 160 65 128 256), losses := [] }

theorem u321 : Upper (D 8) (R 8) [66,5,40,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b322 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 280 112 160 96 129 385), lower := (rows 67 7 44 280 112 160 96 128 256), losses := [] }

theorem u322 : Upper (D 8) (R 8) [66,5,40,272,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 280 112 160 192 161 289), lower := (rows 67 7 44 280 112 160 192 128 256), losses := [] }

theorem u323 : Upper (D 8) (R 8) [66,5,40,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 280 176 96 65 160 416), lower := (rows 67 7 44 280 176 96 65 128 256), losses := [] }

theorem u324 : Upper (D 8) (R 8) [66,5,40,272,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 280 176 96 96 129 385), lower := (rows 67 7 44 280 176 96 96 128 256), losses := [] }

theorem u325 : Upper (D 8) (R 8) [66,5,40,272,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 67 7 44 280 176 96 192 161 289), lower := (rows 67 7 44 280 176 96 192 128 256), losses := [] }

theorem u326 : Upper (D 8) (R 8) [66,5,40,272,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b327 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 392 176 96 65 176 304), lower := (rows 67 7 44 392 176 96 65 128 256), losses := [] }

theorem u327 : Upper (D 8) (R 8) [66,5,40,384,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b328 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 44 392 176 96 80 161 289), lower := (rows 67 7 44 392 176 96 80 128 256), losses := [] }

theorem u328 : Upper (D 8) (R 8) [66,5,40,384,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b328 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b329 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 392 176 96 96 145 273), lower := (rows 67 7 44 392 176 96 96 128 256), losses := [] }

theorem u329 : Upper (D 8) (R 8) [66,5,40,384,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b330 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 67 7 140 56 336 160 65 160 288), lower := (rows 67 7 140 56 336 160 65 128 256), losses := [] }

theorem u330 : Upper (D 8) (R 8) [66,5,136,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b331 : PairBound 9 := { available := 33, camps := [], pairs := [(0,7)], upper := (rows 67 7 140 56 336 160 96 161 289), lower := (rows 67 7 140 56 336 160 96 128 256), losses := [{ target := 7, region := (rows 5 6 4 8 16 32 104 0 256), good := (rows 67 7 79 120 336 96 96 0 256) }] }

theorem u331 : Upper (D 8) (R 8) [66,5,136,48,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 67 7 140 280 112 160 65 160 288), lower := (rows 67 7 140 280 112 160 65 128 256), losses := [] }

theorem u332 : Upper (D 8) (R 8) [66,5,136,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 67 7 140 280 112 160 96 161 289), lower := (rows 67 7 140 280 112 160 96 128 256), losses := [] }

theorem u333 : Upper (D 8) (R 8) [66,5,136,272,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 67 7 140 296 112 160 65 176 304), lower := (rows 67 7 140 296 112 160 65 128 256), losses := [] }

theorem u334 : Upper (D 8) (R 8) [66,5,136,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 140 296 112 160 80 161 289), lower := (rows 67 7 140 296 112 160 80 128 256), losses := [] }

theorem u335 : Upper (D 8) (R 8) [66,5,136,288,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b335 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 67 7 140 296 112 160 96 145 273), lower := (rows 67 7 140 296 112 160 96 128 256), losses := [] }

theorem u336 : Upper (D 8) (R 8) [66,5,136,288,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 296 176 96 65 176 304), lower := (rows 67 7 140 296 176 96 65 128 256), losses := [] }

theorem u337 : Upper (D 8) (R 8) [66,5,136,288,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 140 296 176 96 80 161 289), lower := (rows 67 7 140 296 176 96 80 128 256), losses := [] }

theorem u338 : Upper (D 8) (R 8) [66,5,136,288,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b338 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 296 176 96 96 145 273), lower := (rows 67 7 140 296 176 96 96 128 256), losses := [] }

theorem u339 : Upper (D 8) (R 8) [66,5,136,288,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 56 280 96 65 160 416), lower := (rows 67 7 164 56 280 96 65 128 256), losses := [] }

theorem u340 : Upper (D 8) (R 8) [66,5,160,48,264,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 120, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 164 56 280 96 96 129 385), lower := (rows 67 7 164 56 280 96 96 128 256), losses := [] }

theorem u341 : Upper (D 8) (R 8) [66,5,160,48,264,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 128 }], pairs := [(3,7)], upper := (rows 67 7 164 56 280 96 192 161 289), lower := (rows 67 7 164 56 280 96 192 128 256), losses := [] }

theorem u342 : Upper (D 8) (R 8) [66,5,160,48,264,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 56 400 96 65 168 296), lower := (rows 67 7 164 56 400 96 65 128 256), losses := [] }

theorem u343 : Upper (D 8) (R 8) [66,5,160,48,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 164 56 400 96 72 161 289), lower := (rows 67 7 164 56 400 96 72 128 256), losses := [] }

theorem u344 : Upper (D 8) (R 8) [66,5,160,48,384,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b344 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 164 56 400 96 96 137 265), lower := (rows 67 7 164 56 400 96 96 128 256), losses := [] }

theorem u345 : Upper (D 8) (R 8) [66,5,160,48,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 152 304 96 65 168 296), lower := (rows 67 7 164 152 304 96 65 128 256), losses := [] }

theorem u346 : Upper (D 8) (R 8) [66,5,160,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 164 152 304 96 72 161 289), lower := (rows 67 7 164 152 304 96 72 128 256), losses := [] }

theorem u347 : Upper (D 8) (R 8) [66,5,160,144,288,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b347 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 164 152 304 96 96 137 265), lower := (rows 67 7 164 152 304 96 96 128 256), losses := [] }

theorem u348 : Upper (D 8) (R 8) [66,5,160,144,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 67 7 268 152 112 160 65 160 288), lower := (rows 67 7 268 152 112 160 65 128 256), losses := [] }

theorem u349 : Upper (D 8) (R 8) [66,5,264,144,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 67 7 268 152 112 160 96 161 289), lower := (rows 67 7 268 152 112 160 96 128 256), losses := [] }

theorem u350 : Upper (D 8) (R 8) [66,5,264,144,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 388, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 56 152 96 65 160 416), lower := (rows 67 7 292 56 152 96 65 128 256), losses := [] }

theorem u351 : Upper (D 8) (R 8) [66,5,288,48,136,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 292 56 152 96 96 129 385), lower := (rows 67 7 292 56 152 96 96 128 256), losses := [] }

theorem u352 : Upper (D 8) (R 8) [66,5,288,48,136,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 263, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 292 56 152 96 192 161 289), lower := (rows 67 7 292 56 152 96 192 128 256), losses := [] }

theorem u353 : Upper (D 8) (R 8) [66,5,288,48,136,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 404, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 292 104 152 160 65 176 304), lower := (rows 67 7 292 104 152 160 65 128 256), losses := [] }

theorem u354 : Upper (D 8) (R 8) [66,5,288,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 7 292 104 152 160 80 161 289), lower := (rows 67 7 292 104 152 160 80 128 256), losses := [] }

theorem u355 : Upper (D 8) (R 8) [66,5,288,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b355 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 292 104 152 160 96 145 273), lower := (rows 67 7 292 104 152 160 96 128 256), losses := [] }

theorem u356 : Upper (D 8) (R 8) [66,5,288,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 136, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 21 168 304 96 65 160 416), lower := (rows 67 14 21 168 304 96 65 128 256), losses := [] }

theorem u357 : Upper (D 8) (R 8) [66,12,17,160,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 21 168 304 96 96 129 385), lower := (rows 67 14 21 168 304 96 96 128 256), losses := [] }

theorem u358 : Upper (D 8) (R 8) [66,12,17,160,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 308, targets := 128 }], pairs := [(2,7)], upper := (rows 67 14 21 168 304 96 192 161 289), lower := (rows 67 14 21 168 304 96 192 128 256), losses := [] }

theorem u359 : Upper (D 8) (R 8) [66,12,17,160,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P08
