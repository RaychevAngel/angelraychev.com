import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b300 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 276, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 13 98 52 200 274 160 65 129 258), lower := (rows 13 98 52 200 274 160 65 129 256), losses := [] }

theorem u300 : Upper (D 7) (R 7) [12,96,48,192,258,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 164, targets := 65 },{ cop := 6, region := 170, targets := 1 }], pairs := [(1,0),(2,0),(2,6),(3,0)], upper := (rows 13 98 52 200 274 160 65 130 257), lower := (rows 13 98 52 200 274 160 65 130 256), losses := [] }

theorem u301 : Upper (D 7) (R 7) [12,96,48,192,258,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 52 200 400 33 66 129 258), lower := (rows 13 98 52 200 400 33 66 129 256), losses := [{ target := 0, region := (rows 0 38 4 136 152 32 103 128 359), good := (rows 350 354 374 472 408 354 322 472 256) }] }

theorem u302 : Upper (D 7) (R 7) [12,96,48,192,384,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 200 400 33 66 130 257), lower := (rows 13 98 52 200 400 33 66 130 256), losses := [] }

theorem u303 : Upper (D 7) (R 7) [12,96,48,192,384,1,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 52 200 400 34 65 129 258), lower := (rows 13 98 52 200 400 34 65 129 256), losses := [] }

theorem u304 : Upper (D 7) (R 7) [12,96,48,192,384,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 170, targets := 1 },{ cop := 0, region := 98, targets := 128 },{ cop := 1, region := 136, targets := 32 }], pairs := [(1,0),(1,7),(3,0),(3,5)], upper := (rows 13 98 52 200 400 34 65 130 257), lower := (rows 13 98 52 200 400 34 65 130 256), losses := [] }

theorem u305 : Upper (D 7) (R 7) [12,96,48,192,384,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 264, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 13 98 52 266 146 33 192 129 320), lower := (rows 13 98 52 266 146 33 192 129 256), losses := [] }

theorem u306 : Upper (D 7) (R 7) [12,96,48,258,130,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 52 266 146 33 192 192 257), lower := (rows 13 98 52 266 146 33 192 192 256), losses := [] }

theorem u307 : Upper (D 7) (R 7) [12,96,48,258,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 264, targets := 161 }], pairs := [(1,0),(3,0),(3,5),(3,7)], upper := (rows 13 98 52 328 146 33 192 129 258), lower := (rows 13 98 52 328 146 33 192 129 256), losses := [{ target := 0, region := (rows 0 6 4 158 16 32 208 128 279), good := (rows 270 362 382 328 474 288 200 456 256) }] }

theorem u308 : Upper (D 7) (R 7) [12,96,48,320,130,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 365, targets := 2 },{ cop := 5, region := 194, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 98 52 328 146 33 192 130 257), lower := (rows 13 98 52 328 146 33 192 130 256), losses := [] }

theorem u309 : Upper (D 7) (R 7) [12,96,48,320,130,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 164, targets := 66 }], pairs := [(1,0),(1,7),(2,1),(2,6)], upper := (rows 13 98 52 392 81 160 66 129 258), lower := (rows 13 98 52 392 81 160 66 129 256), losses := [] }

theorem u310 : Upper (D 7) (R 7) [12,96,48,384,65,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 2, region := 66, targets := 128 },{ cop := 8, region := 234, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(3,0)], upper := (rows 13 98 52 392 81 160 66 130 257), lower := (rows 13 98 52 392 81 160 66 130 256), losses := [] }

theorem u311 : Upper (D 7) (R 7) [12,96,48,384,65,128,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 52 392 208 33 66 129 258), lower := (rows 13 98 52 392 208 33 66 129 256), losses := [{ target := 0, region := (rows 0 38 4 152 144 32 103 128 359), good := (rows 334 354 382 408 472 354 322 472 256) }] }

theorem u312 : Upper (D 7) (R 7) [12,96,48,384,192,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 52 392 208 33 66 130 257), lower := (rows 13 98 52 392 208 33 66 130 256), losses := [] }

theorem u313 : Upper (D 7) (R 7) [12,96,48,384,192,1,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 264, targets := 129 },{ cop := 2, region := 361, targets := 2 }], pairs := [(0,1),(3,0),(3,7)], upper := (rows 13 98 134 296 19 33 192 144 320), lower := (rows 13 98 134 296 19 33 192 144 256), losses := [] }

theorem u314 : Upper (D 7) (R 7) [12,96,130,288,3,1,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b314 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 313, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 98 134 296 19 33 192 192 272), lower := (rows 13 98 134 296 19 33 192 192 256), losses := [] }

theorem u315 : Upper (D 7) (R 7) [12,96,130,288,3,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 264, targets := 129 },{ cop := 1, region := 264, targets := 2 }], pairs := [(3,0),(3,1),(3,7)], upper := (rows 13 98 134 296 19 48 192 129 320), lower := (rows 13 98 134 296 19 48 192 129 256), losses := [] }

theorem u316 : Upper (D 7) (R 7) [12,96,130,288,3,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b316 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 313, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 13 98 134 296 19 48 192 192 257), lower := (rows 13 98 134 296 19 48 192 192 256), losses := [] }

theorem u317 : Upper (D 7) (R 7) [12,96,130,288,3,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b317 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 264, targets := 129 },{ cop := 2, region := 361, targets := 2 }], pairs := [(0,1),(3,0),(3,7)], upper := (rows 13 98 134 296 19 160 65 144 320), lower := (rows 13 98 134 296 19 160 65 144 256), losses := [] }

theorem u318 : Upper (D 7) (R 7) [12,96,130,288,3,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b318 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 313, targets := 64 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,6),(1,0),(3,6),(4,6)], upper := (rows 13 98 134 296 19 160 65 192 272), lower := (rows 13 98 134 296 19 160 65 192 256), losses := [] }

theorem u319 : Upper (D 7) (R 7) [12,96,130,288,3,128,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b320 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 264, targets := 129 },{ cop := 1, region := 264, targets := 2 }], pairs := [(3,0),(3,1),(3,7)], upper := (rows 13 98 134 296 19 160 80 129 320), lower := (rows 13 98 134 296 19 160 80 129 256), losses := [] }

theorem u320 : Upper (D 7) (R 7) [12,96,130,288,3,128,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b320 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b321 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 13 98 134 296 19 160 80 192 257), lower := (rows 13 98 134 296 19 160 80 192 256), losses := [] }

theorem u321 : Upper (D 7) (R 7) [12,96,130,288,3,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b321 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b322 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 330, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 13 98 148 296 81 160 66 129 258), lower := (rows 13 98 148 296 81 160 66 129 256), losses := [] }

theorem u322 : Upper (D 7) (R 7) [12,96,144,288,65,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 297, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 98 148 296 81 160 66 130 257), lower := (rows 13 98 148 296 81 160 66 130 256), losses := [] }

theorem u323 : Upper (D 7) (R 7) [12,96,144,288,65,128,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 264, targets := 161 }], pairs := [(3,0),(3,5),(3,7)], upper := (rows 13 98 164 266 146 33 80 129 320), lower := (rows 13 98 164 266 146 33 80 129 256), losses := [] }

theorem u324 : Upper (D 7) (R 7) [12,96,160,258,130,1,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b324 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 266 146 33 80 192 257), lower := (rows 13 98 164 266 146 33 80 192 256), losses := [] }

theorem u325 : Upper (D 7) (R 7) [12,96,160,258,130,1,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b325 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 164 280 146 33 66 129 320), lower := (rows 13 98 164 280 146 33 66 129 256), losses := [] }

theorem u326 : Upper (D 7) (R 7) [12,96,160,272,130,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b327 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 164 280 146 33 66 192 257), lower := (rows 13 98 164 280 146 33 66 192 256), losses := [] }

theorem u327 : Upper (D 7) (R 7) [12,96,160,272,130,1,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b328 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 164 280 208 33 66 129 258), lower := (rows 13 98 164 280 208 33 66 129 256), losses := [] }

theorem u328 : Upper (D 7) (R 7) [12,96,160,272,192,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b329 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 164 280 208 33 66 130 257), lower := (rows 13 98 164 280 208 33 66 130 256), losses := [] }

theorem u329 : Upper (D 7) (R 7) [12,96,160,272,192,1,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b330 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 164 328 146 33 66 129 272), lower := (rows 13 98 164 328 146 33 66 129 256), losses := [] }

theorem u330 : Upper (D 7) (R 7) [12,96,160,320,130,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b331 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 98 164 328 146 33 66 144 257), lower := (rows 13 98 164 328 146 33 66 144 256), losses := [] }

theorem u331 : Upper (D 7) (R 7) [12,96,160,320,130,1,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b331 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 13 98 164 328 146 33 80 129 258), lower := (rows 13 98 164 328 146 33 80 129 256), losses := [] }

theorem u332 : Upper (D 7) (R 7) [12,96,160,320,130,1,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b332 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 365, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 98 164 328 146 33 80 130 257), lower := (rows 13 98 164 328 146 33 80 130 256), losses := [] }

theorem u333 : Upper (D 7) (R 7) [12,96,160,320,130,1,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b333 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 13 259 38 74 145 48 192 160 320), lower := (rows 13 259 38 74 145 48 192 160 256), losses := [] }

theorem u334 : Upper (D 7) (R 7) [12,257,34,66,129,16,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b334 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 294, targets := 192 }], pairs := [(1,6),(1,7),(2,6)], upper := (rows 13 259 38 74 145 48 192 192 288), lower := (rows 13 259 38 74 145 48 192 192 256), losses := [] }

theorem u335 : Upper (D 7) (R 7) [12,257,34,66,129,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b335 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 314, targets := 1 },{ cop := 2, region := 176, targets := 64 }], pairs := [(1,0),(3,0),(4,0),(4,6)], upper := (rows 13 274 7 104 176 34 192 129 320), lower := (rows 13 274 7 104 176 34 192 129 256), losses := [] }

theorem u336 : Upper (D 7) (R 7) [12,272,3,96,160,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 216, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 13 274 7 104 176 34 192 192 257), lower := (rows 13 274 7 104 176 34 192 192 256), losses := [] }

theorem u337 : Upper (D 7) (R 7) [12,272,3,96,160,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 },{ cop := 5, region := 338, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 13 274 37 74 146 160 96 129 320), lower := (rows 13 274 37 74 146 160 96 129 256), losses := [] }

theorem u338 : Upper (D 7) (R 7) [12,272,33,66,130,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 274 37 74 146 160 96 192 257), lower := (rows 13 274 37 74 146 160 96 192 256), losses := [] }

theorem u339 : Upper (D 7) (R 7) [12,272,33,66,130,128,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 128, camps := [{ cop := 7, region := 378, targets := 1 },{ cop := 4, region := 258, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 7 88 176 96 66 129 384), lower := (rows 13 290 7 88 176 96 66 129 256), losses := [] }

theorem u340 : Upper (D 7) (R 7) [12,288,3,80,160,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 205, targets := 32 },{ cop := 5, region := 338, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 290 7 200 112 160 66 129 272), lower := (rows 13 290 7 200 112 160 66 129 256), losses := [] }

theorem u341 : Upper (D 7) (R 7) [12,288,3,192,96,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 13 290 7 200 112 160 66 144 257), lower := (rows 13 290 7 200 112 160 66 144 256), losses := [] }

theorem u342 : Upper (D 7) (R 7) [12,288,3,192,96,128,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b342 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 },{ cop := 6, region := 290, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 13 290 21 74 176 34 192 129 320), lower := (rows 13 290 21 74 176 34 192 129 256), losses := [] }

theorem u343 : Upper (D 7) (R 7) [12,288,17,66,160,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 0, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 74 176 34 192 192 257), lower := (rows 13 290 21 74 176 34 192 192 256), losses := [] }

theorem u344 : Upper (D 7) (R 7) [12,288,17,66,160,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 13 290 37 74 146 48 192 129 320), lower := (rows 13 290 37 74 146 48 192 129 256), losses := [] }

theorem u345 : Upper (D 7) (R 7) [12,288,33,66,130,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b345 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 290 37 74 146 48 192 192 257), lower := (rows 13 290 37 74 146 48 192 192 256), losses := [] }

theorem u346 : Upper (D 7) (R 7) [12,288,33,66,130,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b346 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 266, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 13 290 52 74 145 96 192 129 258), lower := (rows 13 290 52 74 145 96 192 129 256), losses := [] }

theorem u347 : Upper (D 7) (R 7) [12,288,48,66,129,64,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 234, targets := 1 },{ cop := 1, region := 200, targets := 32 },{ cop := 4, region := 100, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(3,5)], upper := (rows 13 290 52 74 145 96 192 130 257), lower := (rows 13 290 52 74 145 96 192 130 256), losses := [] }

theorem u348 : Upper (D 7) (R 7) [12,288,48,66,129,64,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 258, targets := 193 },{ cop := 4, region := 173, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(1,7)], upper := (rows 13 290 52 200 82 160 65 129 258), lower := (rows 13 290 52 200 82 160 65 129 256), losses := [] }

theorem u349 : Upper (D 7) (R 7) [12,288,48,192,66,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 172, targets := 1 },{ cop := 8, region := 162, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(3,0)], upper := (rows 13 290 52 200 82 160 65 130 257), lower := (rows 13 290 52 200 82 160 65 130 256), losses := [] }

theorem u350 : Upper (D 7) (R 7) [12,288,48,192,66,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 189, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 290 69 152 112 160 66 129 258), lower := (rows 13 290 69 152 112 160 66 129 256), losses := [] }

theorem u351 : Upper (D 7) (R 7) [12,288,65,144,96,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 69 152 112 160 66 130 257), lower := (rows 13 290 69 152 112 160 66 130 256), losses := [] }

theorem u352 : Upper (D 7) (R 7) [12,288,65,144,96,128,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 141, targets := 2 },{ cop := 7, region := 370, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 290 69 168 146 96 66 129 272), lower := (rows 13 290 69 168 146 96 66 129 256), losses := [] }

theorem u353 : Upper (D 7) (R 7) [12,288,65,160,130,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 69 168 146 96 66 144 257), lower := (rows 13 290 69 168 146 96 66 144 256), losses := [] }

theorem u354 : Upper (D 7) (R 7) [12,288,65,160,130,64,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b354 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 221, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 290 70 152 19 96 192 129 288), lower := (rows 13 290 70 152 19 96 192 129 256), losses := [] }

theorem u355 : Upper (D 7) (R 7) [12,288,66,144,3,64,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 232, targets := 2 },{ cop := 8, region := 226, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(3,1)], upper := (rows 13 290 70 152 19 96 192 160 257), lower := (rows 13 290 70 152 19 96 192 160 256), losses := [] }

theorem u356 : Upper (D 7) (R 7) [12,288,66,144,3,64,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 262, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 290 70 152 112 160 65 129 258), lower := (rows 13 290 70 152 112 160 65 129 256), losses := [] }

theorem u357 : Upper (D 7) (R 7) [12,288,66,144,96,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 184, targets := 1 },{ cop := 8, region := 162, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 70 152 112 160 65 130 257), lower := (rows 13 290 70 152 112 160 65 130 256), losses := [] }

theorem u358 : Upper (D 7) (R 7) [12,288,66,144,96,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 13 290 70 168 19 33 192 144 320), lower := (rows 13 290 70 168 19 33 192 144 256), losses := [] }

theorem u359 : Upper (D 7) (R 7) [12,288,66,160,3,1,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b359 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P07
