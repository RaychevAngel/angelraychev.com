import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b300 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 134 100 41 276 48 66 129 320), lower := (rows 11 134 100 41 276 48 66 129 256), losses := [] }

theorem u300 : Upper (D 6) (R 6) [10,132,96,33,260,16,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b300 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 134 100 41 276 48 66 192 257), lower := (rows 11 134 100 41 276 48 66 192 256), losses := [] }

theorem u301 : Upper (D 6) (R 6) [10,132,96,33,260,16,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b301 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 134 100 56 336 33 66 129 260), lower := (rows 11 134 100 56 336 33 66 129 256), losses := [] }

theorem u302 : Upper (D 6) (R 6) [10,132,96,48,320,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 377, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 100 56 336 33 66 132 257), lower := (rows 11 134 100 56 336 33 66 132 256), losses := [] }

theorem u303 : Upper (D 6) (R 6) [10,132,96,48,320,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 134 100 56 336 34 65 129 260), lower := (rows 11 134 100 56 336 34 65 129 256), losses := [] }

theorem u304 : Upper (D 6) (R 6) [10,132,96,48,320,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 377, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 134 100 56 336 34 65 132 257), lower := (rows 11 134 100 56 336 34 65 132 256), losses := [] }

theorem u305 : Upper (D 6) (R 6) [10,132,96,48,320,2,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 261 25 52 96 66 160 320), lower := (rows 11 134 261 25 52 96 66 160 256), losses := [] }

theorem u306 : Upper (D 6) (R 6) [10,132,257,17,36,64,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 203, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 261 25 52 96 66 192 288), lower := (rows 11 134 261 25 52 96 66 192 256), losses := [] }

theorem u307 : Upper (D 6) (R 6) [10,132,257,17,36,64,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 333, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 134 261 28 50 96 65 160 320), lower := (rows 11 134 261 28 50 96 65 160 256), losses := [] }

theorem u308 : Upper (D 6) (R 6) [10,132,257,20,34,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 134 261 28 50 96 65 192 288), lower := (rows 11 134 261 28 50 96 65 192 256), losses := [] }

theorem u309 : Upper (D 6) (R 6) [10,132,257,20,34,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 147, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 261 44 50 96 65 144 320), lower := (rows 11 134 261 44 50 96 65 144 256), losses := [] }

theorem u310 : Upper (D 6) (R 6) [10,132,257,36,34,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b310 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 134 261 44 50 96 65 192 272), lower := (rows 11 134 261 44 50 96 65 192 256), losses := [] }

theorem u311 : Upper (D 6) (R 6) [10,132,257,36,34,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 262 28 49 96 96 129 320), lower := (rows 11 134 262 28 49 96 96 129 256), losses := [] }

theorem u312 : Upper (D 6) (R 6) [10,132,258,20,33,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 260, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 134 262 28 49 96 96 192 257), lower := (rows 11 134 262 28 49 96 96 192 256), losses := [] }

theorem u313 : Upper (D 6) (R 6) [10,132,258,20,33,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 262 56 84 33 96 129 320), lower := (rows 11 134 262 56 84 33 96 129 256), losses := [] }

theorem u314 : Upper (D 6) (R 6) [10,132,258,48,68,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 130, targets := 33 },{ cop := 0, region := 260, targets := 32 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 11 134 262 56 84 33 96 192 257), lower := (rows 11 134 262 56 84 33 96 192 256), losses := [] }

theorem u315 : Upper (D 6) (R 6) [10,132,258,48,68,1,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 292 25 112 34 68 129 320), lower := (rows 11 134 292 25 112 34 68 129 256), losses := [] }

theorem u316 : Upper (D 6) (R 6) [10,132,288,17,96,2,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 292 25 112 34 68 192 257), lower := (rows 11 134 292 25 112 34 68 192 256), losses := [] }

theorem u317 : Upper (D 6) (R 6) [10,132,288,17,96,2,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 292 56 84 34 65 129 320), lower := (rows 11 134 292 56 84 34 65 129 256), losses := [] }

theorem u318 : Upper (D 6) (R 6) [10,132,288,48,68,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 170, targets := 1 },{ cop := 0, region := 292, targets := 64 }], pairs := [(1,0),(2,6),(3,0)], upper := (rows 11 134 292 56 84 34 65 192 257), lower := (rows 11 134 292 56 84 34 65 192 256), losses := [] }

theorem u319 : Upper (D 6) (R 6) [10,132,288,48,68,2,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b320 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 151, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 38 296 21 96 65 132 320), lower := (rows 11 146 38 296 21 96 65 132 256), losses := [] }

theorem u320 : Upper (D 6) (R 6) [10,144,34,288,5,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b321 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 146 38 296 21 96 65 192 260), lower := (rows 11 146 38 296 21 96 65 192 256), losses := [] }

theorem u321 : Upper (D 6) (R 6) [10,144,34,288,5,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b322 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 146 100 13 304 34 68 129 320), lower := (rows 11 146 100 13 304 34 68 129 256), losses := [] }

theorem u322 : Upper (D 6) (R 6) [10,144,96,5,288,2,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 13 304 34 68 192 257), lower := (rows 11 146 100 13 304 34 68 192 256), losses := [] }

theorem u323 : Upper (D 6) (R 6) [10,144,96,5,288,2,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 146 100 13 304 36 66 129 320), lower := (rows 11 146 100 13 304 36 66 129 256), losses := [] }

theorem u324 : Upper (D 6) (R 6) [10,144,96,5,288,4,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 13 304 36 66 192 257), lower := (rows 11 146 100 13 304 36 66 192 256), losses := [] }

theorem u325 : Upper (D 6) (R 6) [10,144,96,5,288,4,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 147, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 146 262 44 21 96 65 160 320), lower := (rows 11 146 262 44 21 96 65 160 256), losses := [] }

theorem u326 : Upper (D 6) (R 6) [10,144,258,36,5,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b327 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 211, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 146 262 44 21 96 65 192 288), lower := (rows 11 146 262 44 21 96 65 192 256), losses := [] }

theorem u327 : Upper (D 6) (R 6) [10,144,258,36,5,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b328 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 219, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 292 13 84 96 66 129 288), lower := (rows 11 146 292 13 84 96 66 129 256), losses := [] }

theorem u328 : Upper (D 6) (R 6) [10,144,288,5,68,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b329 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 13 84 96 66 160 257), lower := (rows 11 146 292 13 84 96 66 160 256), losses := [] }

theorem u329 : Upper (D 6) (R 6) [10,144,288,5,68,64,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b330 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 146 292 13 112 34 68 129 320), lower := (rows 11 146 292 13 112 34 68 129 256), losses := [] }

theorem u330 : Upper (D 6) (R 6) [10,144,288,5,96,2,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b331 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 178, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 146 292 13 112 34 68 192 257), lower := (rows 11 146 292 13 112 34 68 192 256), losses := [] }

theorem u331 : Upper (D 6) (R 6) [10,144,288,5,96,2,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 22 73 304 96 68 129 260), lower := (rows 11 162 22 73 304 96 68 129 256), losses := [] }

theorem u332 : Upper (D 6) (R 6) [10,160,18,65,288,64,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 22 73 304 96 68 132 257), lower := (rows 11 162 22 73 304 96 68 132 256), losses := [] }

theorem u333 : Upper (D 6) (R 6) [10,160,18,65,288,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 276, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 162 22 76 304 96 65 129 260), lower := (rows 11 162 22 76 304 96 65 129 256), losses := [] }

theorem u334 : Upper (D 6) (R 6) [10,160,18,68,288,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 22 76 304 96 65 132 257), lower := (rows 11 162 22 76 304 96 65 132 256), losses := [] }

theorem u335 : Upper (D 6) (R 6) [10,160,18,68,288,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 130, targets := 4 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 11 162 37 280 82 96 68 129 260), lower := (rows 11 162 37 280 82 96 68 129 256), losses := [] }

theorem u336 : Upper (D 6) (R 6) [10,160,33,272,66,64,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 37 280 82 96 68 132 257), lower := (rows 11 162 37 280 82 96 68 132 256), losses := [] }

theorem u337 : Upper (D 6) (R 6) [10,160,33,272,66,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 52 73 274 96 68 129 260), lower := (rows 11 162 52 73 274 96 68 129 256), losses := [] }

theorem u338 : Upper (D 6) (R 6) [10,160,48,65,258,64,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 52 73 274 96 68 132 257), lower := (rows 11 162 52 73 274 96 68 132 256), losses := [] }

theorem u339 : Upper (D 6) (R 6) [10,160,48,65,258,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 276, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 162 52 76 274 96 65 129 260), lower := (rows 11 162 52 76 274 96 65 129 256), losses := [] }

theorem u340 : Upper (D 6) (R 6) [10,160,48,68,258,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 130, targets := 65 },{ cop := 0, region := 272, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 162 52 76 274 96 65 132 257), lower := (rows 11 162 52 76 274 96 65 132 256), losses := [] }

theorem u341 : Upper (D 6) (R 6) [10,160,48,68,258,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 276, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 162 52 76 276 96 65 129 258), lower := (rows 11 162 52 76 276 96 65 129 256), losses := [] }

theorem u342 : Upper (D 6) (R 6) [10,160,48,68,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 380, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 162 52 76 276 96 65 130 257), lower := (rows 11 162 52 76 276 96 65 130 256), losses := [] }

theorem u343 : Upper (D 6) (R 6) [10,160,48,68,260,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 348, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 162 52 76 336 33 66 129 260), lower := (rows 11 162 52 76 336 33 66 129 256), losses := [] }

theorem u344 : Upper (D 6) (R 6) [10,160,48,68,320,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 202, targets := 1 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,0),(3,0)], upper := (rows 11 162 52 76 336 33 66 132 257), lower := (rows 11 162 52 76 336 33 66 132 256), losses := [] }

theorem u345 : Upper (D 6) (R 6) [10,160,48,68,320,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 348, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 162 52 328 84 33 66 129 260), lower := (rows 11 162 52 328 84 33 66 129 256), losses := [] }

theorem u346 : Upper (D 6) (R 6) [10,160,48,320,68,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 52 328 84 33 66 132 257), lower := (rows 11 162 52 328 84 33 66 132 256), losses := [] }

theorem u347 : Upper (D 6) (R 6) [10,160,48,320,68,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 162 69 28 274 33 96 132 320), lower := (rows 11 162 69 28 274 33 96 132 256), losses := [] }

theorem u348 : Upper (D 6) (R 6) [10,160,65,20,258,1,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 162 69 28 274 33 96 192 260), lower := (rows 11 162 69 28 274 33 96 192 256), losses := [] }

theorem u349 : Upper (D 6) (R 6) [10,160,65,20,258,1,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 162 70 28 304 96 65 129 260), lower := (rows 11 162 70 28 304 96 65 129 256), losses := [] }

theorem u350 : Upper (D 6) (R 6) [10,160,66,20,288,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 162 70 28 304 96 65 132 257), lower := (rows 11 162 70 28 304 96 65 132 256), losses := [] }

theorem u351 : Upper (D 6) (R 6) [10,160,66,20,288,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 162 70 56 336 36 65 129 260), lower := (rows 11 162 70 56 336 36 65 129 256), losses := [] }

theorem u352 : Upper (D 6) (R 6) [10,160,66,48,320,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 70 56 336 36 65 132 257), lower := (rows 11 162 70 56 336 36 65 132 256), losses := [] }

theorem u353 : Upper (D 6) (R 6) [10,160,66,48,320,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 162 70 88 52 288 65 129 260), lower := (rows 11 162 70 88 52 288 65 129 256), losses := [] }

theorem u354 : Upper (D 6) (R 6) [10,160,66,80,36,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b354 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 130, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 162 70 88 52 288 65 132 257), lower := (rows 11 162 70 88 52 288 65 132 256), losses := [] }

theorem u355 : Upper (D 6) (R 6) [10,160,66,80,36,256,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b355 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 162 70 88 304 36 65 129 260), lower := (rows 11 162 70 88 304 36 65 129 256), losses := [] }

theorem u356 : Upper (D 6) (R 6) [10,160,66,80,288,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 70 88 304 36 65 132 257), lower := (rows 11 162 70 88 304 36 65 132 256), losses := [] }

theorem u357 : Upper (D 6) (R 6) [10,160,66,80,288,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 70 328 49 36 65 132 272), lower := (rows 11 162 70 328 49 36 65 132 256), losses := [] }

theorem u358 : Upper (D 6) (R 6) [10,160,66,320,33,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 70 328 49 36 65 144 260), lower := (rows 11 162 70 328 49 36 65 144 256), losses := [] }

theorem u359 : Upper (D 6) (R 6) [10,160,66,320,33,4,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b359 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P06
