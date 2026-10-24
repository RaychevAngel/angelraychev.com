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

def b9420 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 56 208 34 65 130 386), lower := (rows 37 266 69 56 208 34 65 128 256), losses := [] }

theorem u9420 : Upper (D 7) (R 7) [36,264,65,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9421 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 144, targets := 34 }], pairs := [(0,7),(2,7),(4,1),(4,5)], upper := (rows 37 266 69 56 208 34 66 129 385), lower := (rows 37 266 69 56 208 34 66 128 256), losses := [] }

theorem u9421 : Upper (D 7) (R 7) [36,264,65,48,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9422 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 69 56 208 34 192 131 259), lower := (rows 37 266 69 56 208 34 192 128 256), losses := [] }

theorem u9422 : Upper (D 7) (R 7) [36,264,65,48,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9423 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 266 69 74 50 160 65 144 400), lower := (rows 37 266 69 74 50 160 65 128 256), losses := [] }

theorem u9423 : Upper (D 7) (R 7) [36,264,65,66,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9424 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 266 69 74 50 160 80 129 385), lower := (rows 37 266 69 74 50 160 80 128 256), losses := [] }

theorem u9424 : Upper (D 7) (R 7) [36,264,65,66,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9424 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9425 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 266 69 74 50 160 192 145 273), lower := (rows 37 266 69 74 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 224 224 128 256), good := (rows 100 282 100 122 122 224 224 224 256) }] }

theorem u9425 : Upper (D 7) (R 7) [36,264,65,66,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9426 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 74, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 266 69 74 145 48 66 160 416), lower := (rows 37 266 69 74 145 48 66 128 256), losses := [] }

theorem u9426 : Upper (D 7) (R 7) [36,264,65,66,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9426 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9427 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 266 69 74 145 48 96 130 386), lower := (rows 37 266 69 74 145 48 96 128 256), losses := [] }

theorem u9427 : Upper (D 7) (R 7) [36,264,65,66,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9427 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9428 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 266 69 74 145 48 192 162 290), lower := (rows 37 266 69 74 145 48 192 128 256), losses := [] }

theorem u9428 : Upper (D 7) (R 7) [36,264,65,66,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9428 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9429 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 74, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 266 69 74 145 160 66 176 304), lower := (rows 37 266 69 74 145 160 66 128 256), losses := [] }

theorem u9429 : Upper (D 7) (R 7) [36,264,65,66,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9430 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 266 69 74 145 160 80 162 290), lower := (rows 37 266 69 74 145 160 80 128 256), losses := [] }

theorem u9430 : Upper (D 7) (R 7) [36,264,65,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9430 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9431 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 74 145 160 96 146 274), lower := (rows 37 266 69 74 145 160 96 128 256), losses := [] }

theorem u9431 : Upper (D 7) (R 7) [36,264,65,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9432 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 266 69 74 146 48 65 160 416), lower := (rows 37 266 69 74 146 48 65 128 256), losses := [] }

theorem u9432 : Upper (D 7) (R 7) [36,264,65,66,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9432 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9433 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 37 266 69 74 146 48 96 129 385), lower := (rows 37 266 69 74 146 48 96 128 256), losses := [] }

theorem u9433 : Upper (D 7) (R 7) [36,264,65,66,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9433 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9434 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 101, targets := 2 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 37 266 69 74 146 48 192 161 289), lower := (rows 37 266 69 74 146 48 192 128 256), losses := [] }

theorem u9434 : Upper (D 7) (R 7) [36,264,65,66,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9434 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9435 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 266 69 74 146 160 65 176 304), lower := (rows 37 266 69 74 146 160 65 128 256), losses := [] }

theorem u9435 : Upper (D 7) (R 7) [36,264,65,66,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9436 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 4, region := 72, targets := 32 }], pairs := [(0,1),(0,6),(3,5)], upper := (rows 37 266 69 74 146 160 80 161 289), lower := (rows 37 266 69 74 146 160 80 128 256), losses := [] }

theorem u9436 : Upper (D 7) (R 7) [36,264,65,66,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9436 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9437 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 74 146 160 96 145 273), lower := (rows 37 266 69 74 146 160 96 128 256), losses := [] }

theorem u9437 : Upper (D 7) (R 7) [36,264,65,66,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9438 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 266 69 88 19 160 66 160 416), lower := (rows 37 266 69 88 19 160 66 128 256), losses := [] }

theorem u9438 : Upper (D 7) (R 7) [36,264,65,80,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9439 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 88 19 160 96 130 386), lower := (rows 37 266 69 88 19 160 96 128 256), losses := [] }

theorem u9439 : Upper (D 7) (R 7) [36,264,65,80,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9440 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 266 69 88 19 160 192 162 290), lower := (rows 37 266 69 88 19 160 192 128 256), losses := [] }

theorem u9440 : Upper (D 7) (R 7) [36,264,65,80,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9441 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 88 50 160 65 130 386), lower := (rows 37 266 69 88 50 160 65 128 256), losses := [] }

theorem u9441 : Upper (D 7) (R 7) [36,264,65,80,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9442 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 266 69 88 50 160 66 129 385), lower := (rows 37 266 69 88 50 160 66 128 256), losses := [] }

theorem u9442 : Upper (D 7) (R 7) [36,264,65,80,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9443 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(3,1)], upper := (rows 37 266 69 88 50 160 192 131 259), lower := (rows 37 266 69 88 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 100 266 100 120 122 224 224 224 256) },{ target := 1, region := (rows 253 0 253 24 16 224 224 128 256), good := (rows 101 269 101 125 125 229 229 229 256) }] }

theorem u9443 : Upper (D 7) (R 7) [36,264,65,80,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9444 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 266 69 88 146 160 65 162 290), lower := (rows 37 266 69 88 146 160 65 128 256), losses := [] }

theorem u9444 : Upper (D 7) (R 7) [36,264,65,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9445 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 4, region := 72, targets := 160 }], pairs := [(0,1),(0,6),(3,5),(3,7)], upper := (rows 37 266 69 88 146 160 66 161 289), lower := (rows 37 266 69 88 146 160 66 128 256), losses := [] }

theorem u9445 : Upper (D 7) (R 7) [36,264,65,80,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9446 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 88 146 160 96 131 259), lower := (rows 37 266 69 88 146 160 96 128 256), losses := [] }

theorem u9446 : Upper (D 7) (R 7) [36,264,65,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9447 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 88 176 34 65 130 386), lower := (rows 37 266 69 88 176 34 65 128 256), losses := [] }

theorem u9447 : Upper (D 7) (R 7) [36,264,65,80,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9448 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,6)], upper := (rows 37 266 69 88 176 34 66 129 385), lower := (rows 37 266 69 88 176 34 66 128 256), losses := [] }

theorem u9448 : Upper (D 7) (R 7) [36,264,65,80,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9449 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 266 69 88 176 34 192 131 259), lower := (rows 37 266 69 88 176 34 192 128 256), losses := [] }

theorem u9449 : Upper (D 7) (R 7) [36,264,65,80,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9450 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 173, targets := 2 },{ cop := 1, region := 80, targets := 32 }], pairs := [(0,1),(2,1),(3,1),(4,5)], upper := (rows 37 266 69 137 82 160 66 176 304), lower := (rows 37 266 69 137 82 160 66 128 256), losses := [] }

theorem u9450 : Upper (D 7) (R 7) [36,264,65,129,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9451 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 69 137 82 160 80 162 290), lower := (rows 37 266 69 137 82 160 80 128 256), losses := [] }

theorem u9451 : Upper (D 7) (R 7) [36,264,65,129,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9451 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9452 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 137 82 160 96 146 274), lower := (rows 37 266 69 137 82 160 96 128 256), losses := [] }

theorem u9452 : Upper (D 7) (R 7) [36,264,65,129,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9453 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 266 69 137 176 34 66 208 336), lower := (rows 37 266 69 137 176 34 66 128 256), losses := [] }

theorem u9453 : Upper (D 7) (R 7) [36,264,65,129,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9454 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 266 69 137 176 34 80 194 322), lower := (rows 37 266 69 137 176 34 80 128 256), losses := [] }

theorem u9454 : Upper (D 7) (R 7) [36,264,65,129,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9454 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9455 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 266 69 137 208 34 66 176 304), lower := (rows 37 266 69 137 208 34 66 128 256), losses := [] }

theorem u9455 : Upper (D 7) (R 7) [36,264,65,129,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9456 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 37 266 69 137 208 34 80 162 290), lower := (rows 37 266 69 137 208 34 80 128 256), losses := [] }

theorem u9456 : Upper (D 7) (R 7) [36,264,65,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9456 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9457 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 137 208 34 96 146 274), lower := (rows 37 266 69 137 208 34 96 128 256), losses := [] }

theorem u9457 : Upper (D 7) (R 7) [36,264,65,129,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9458 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 266 69 138 82 160 65 176 304), lower := (rows 37 266 69 138 82 160 65 128 256), losses := [] }

theorem u9458 : Upper (D 7) (R 7) [36,264,65,130,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9459 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 37 266 69 138 82 160 80 161 289), lower := (rows 37 266 69 138 82 160 80 128 256), losses := [] }

theorem u9459 : Upper (D 7) (R 7) [36,264,65,130,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9459 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9460 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 138 82 160 96 145 273), lower := (rows 37 266 69 138 82 160 96 128 256), losses := [] }

theorem u9460 : Upper (D 7) (R 7) [36,264,65,130,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9461 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 181, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 266 69 138 145 48 66 224 352), lower := (rows 37 266 69 138 145 48 66 128 256), losses := [] }

theorem u9461 : Upper (D 7) (R 7) [36,264,65,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9461 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9462 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 266 69 138 145 48 96 194 322), lower := (rows 37 266 69 138 145 48 96 128 256), losses := [] }

theorem u9462 : Upper (D 7) (R 7) [36,264,65,130,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9462 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9463 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 266 69 138 208 34 65 176 304), lower := (rows 37 266 69 138 208 34 65 128 256), losses := [] }

theorem u9463 : Upper (D 7) (R 7) [36,264,65,130,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9464 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 69 138 208 34 80 161 289), lower := (rows 37 266 69 138 208 34 80 128 256), losses := [] }

theorem u9464 : Upper (D 7) (R 7) [36,264,65,130,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9464 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9465 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 266 69 138 208 34 96 145 273), lower := (rows 37 266 69 138 208 34 96 128 256), losses := [] }

theorem u9465 : Upper (D 7) (R 7) [36,264,65,130,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9466 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 68, targets := 160 }], pairs := [(1,0),(2,5),(2,7),(3,0)], upper := (rows 37 266 69 152 19 160 66 224 352), lower := (rows 37 266 69 152 19 160 66 128 256), losses := [] }

theorem u9466 : Upper (D 7) (R 7) [36,264,65,144,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9467 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 152 19 160 96 194 322), lower := (rows 37 266 69 152 19 160 96 128 256), losses := [] }

theorem u9467 : Upper (D 7) (R 7) [36,264,65,144,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9468 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 266 69 152 82 160 65 162 290), lower := (rows 37 266 69 152 82 160 65 128 256), losses := [] }

theorem u9468 : Upper (D 7) (R 7) [36,264,65,144,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9469 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 266 69 152 82 160 66 161 289), lower := (rows 37 266 69 152 82 160 66 128 256), losses := [] }

theorem u9469 : Upper (D 7) (R 7) [36,264,65,144,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9470 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 152 82 160 96 131 259), lower := (rows 37 266 69 152 82 160 96 128 256), losses := [] }

theorem u9470 : Upper (D 7) (R 7) [36,264,65,144,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9471 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 168 82 34 65 144 400), lower := (rows 37 266 69 168 82 34 65 128 256), losses := [] }

theorem u9471 : Upper (D 7) (R 7) [36,264,65,160,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9472 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 266 69 168 82 34 80 129 385), lower := (rows 37 266 69 168 82 34 80 128 256), losses := [] }

theorem u9472 : Upper (D 7) (R 7) [36,264,65,160,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9472 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9473 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 2 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 168 82 34 192 145 273), lower := (rows 37 266 69 168 82 34 192 128 256), losses := [] }

theorem u9473 : Upper (D 7) (R 7) [36,264,65,160,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9474 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 144, targets := 34 }], pairs := [(0,7),(2,7),(4,1),(4,5)], upper := (rows 37 266 69 168 145 34 66 208 336), lower := (rows 37 266 69 168 145 34 66 128 256), losses := [] }

theorem u9474 : Upper (D 7) (R 7) [36,264,65,160,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9475 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 266 69 168 145 34 80 194 322), lower := (rows 37 266 69 168 145 34 80 128 256), losses := [] }

theorem u9475 : Upper (D 7) (R 7) [36,264,65,160,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9475 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9476 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 266 69 168 208 34 65 146 274), lower := (rows 37 266 69 168 208 34 65 128 256), losses := [] }

theorem u9476 : Upper (D 7) (R 7) [36,264,65,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9477 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 144, targets := 34 }], pairs := [(0,7),(2,7),(4,1),(4,5)], upper := (rows 37 266 69 168 208 34 66 145 273), lower := (rows 37 266 69 168 208 34 66 128 256), losses := [] }

theorem u9477 : Upper (D 7) (R 7) [36,264,65,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9478 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 69 168 208 34 80 131 259), lower := (rows 37 266 69 168 208 34 80 128 256), losses := [] }

theorem u9478 : Upper (D 7) (R 7) [36,264,65,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9478 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9479 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 266 69 200 19 34 80 160 416), lower := (rows 37 266 69 200 19 34 80 128 256), losses := [] }

theorem u9479 : Upper (D 7) (R 7) [36,264,65,192,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9479 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9479
end Delivery.IrregularNine14.P07
