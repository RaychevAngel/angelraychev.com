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

def b8580 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 1, region := 293, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 37 194 69 26 56 288 66 129 385), lower := (rows 37 194 69 26 56 288 66 128 256), losses := [] }

theorem u8580 : Upper (D 7) (R 7) [36,192,65,18,40,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8580 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8581 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 26 56 288 192 131 259), lower := (rows 37 194 69 26 56 288 192 128 256), losses := [] }

theorem u8581 : Upper (D 7) (R 7) [36,192,65,18,40,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8581 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8582 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 26 176 288 65 138 266), lower := (rows 37 194 69 26 176 288 65 128 256), losses := [] }

theorem u8582 : Upper (D 7) (R 7) [36,192,65,18,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8582 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8583 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 69 26 176 288 66 137 265), lower := (rows 37 194 69 26 176 288 66 128 256), losses := [] }

theorem u8583 : Upper (D 7) (R 7) [36,192,65,18,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8583 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8584 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 37 194 69 26 176 288 72 131 259), lower := (rows 37 194 69 26 176 288 72 128 256), losses := [] }

theorem u8584 : Upper (D 7) (R 7) [36,192,65,18,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8584 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8585 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 194 69 26 273 40 66 160 416), lower := (rows 37 194 69 26 273 40 66 128 256), losses := [] }

theorem u8585 : Upper (D 7) (R 7) [36,192,65,18,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8585 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8586 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 26 273 40 96 130 386), lower := (rows 37 194 69 26 273 40 96 128 256), losses := [] }

theorem u8586 : Upper (D 7) (R 7) [36,192,65,18,257,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8586 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8587 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 26 273 40 192 162 290), lower := (rows 37 194 69 26 273 40 192 128 256), losses := [] }

theorem u8587 : Upper (D 7) (R 7) [36,192,65,18,257,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8587 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8588 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 26 280 160 65 162 290), lower := (rows 37 194 69 26 280 160 65 128 256), losses := [] }

theorem u8588 : Upper (D 7) (R 7) [36,192,65,18,264,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8589 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 2, region := 161, targets := 64 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(1,0),(2,1)], upper := (rows 37 194 69 26 280 160 66 161 289), lower := (rows 37 194 69 26 280 160 66 128 256), losses := [] }

theorem u8589 : Upper (D 7) (R 7) [36,192,65,18,264,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8590 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 69 26 280 160 96 131 259), lower := (rows 37 194 69 26 280 160 96 128 256), losses := [] }

theorem u8590 : Upper (D 7) (R 7) [36,192,65,18,264,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8591 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 26 304 34 65 136 392), lower := (rows 37 194 69 26 304 34 65 128 256), losses := [] }

theorem u8591 : Upper (D 7) (R 7) [36,192,65,18,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8592 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 194 69 26 304 34 72 129 385), lower := (rows 37 194 69 26 304 34 72 128 256), losses := [] }

theorem u8592 : Upper (D 7) (R 7) [36,192,65,18,288,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8592 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8593 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 69 26 304 34 192 137 265), lower := (rows 37 194 69 26 304 34 192 128 256), losses := [] }

theorem u8593 : Upper (D 7) (R 7) [36,192,65,18,288,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8594 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 26 304 40 65 130 386), lower := (rows 37 194 69 26 304 40 65 128 256), losses := [] }

theorem u8594 : Upper (D 7) (R 7) [36,192,65,18,288,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8594 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8595 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 37 194 69 26 304 40 66 129 385), lower := (rows 37 194 69 26 304 40 66 128 256), losses := [] }

theorem u8595 : Upper (D 7) (R 7) [36,192,65,18,288,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8595 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8596 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 26 304 40 192 131 259), lower := (rows 37 194 69 26 304 40 192 128 256), losses := [] }

theorem u8596 : Upper (D 7) (R 7) [36,192,65,18,288,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8596 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8597 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 26 304 160 65 138 266), lower := (rows 37 194 69 26 304 160 65 128 256), losses := [] }

theorem u8597 : Upper (D 7) (R 7) [36,192,65,18,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8598 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 5, region := 66, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(0,1),(1,0),(1,5),(2,1)], upper := (rows 37 194 69 26 304 160 66 137 265), lower := (rows 37 194 69 26 304 160 66 128 256), losses := [] }

theorem u8598 : Upper (D 7) (R 7) [36,192,65,18,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8599 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 2, region := 130, targets := 32 }], pairs := [(0,1),(1,5),(2,1)], upper := (rows 37 194 69 26 304 160 72 131 259), lower := (rows 37 194 69 26 304 160 72 128 256), losses := [] }

theorem u8599 : Upper (D 7) (R 7) [36,192,65,18,288,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8599 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8600 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 26 400 34 65 168 296), lower := (rows 37 194 69 26 400 34 65 128 256), losses := [] }

theorem u8600 : Upper (D 7) (R 7) [36,192,65,18,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8601 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 194 69 26 400 34 72 161 289), lower := (rows 37 194 69 26 400 34 72 128 256), losses := [] }

theorem u8601 : Upper (D 7) (R 7) [36,192,65,18,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8601 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8602 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 69 26 400 34 96 137 265), lower := (rows 37 194 69 26 400 34 96 128 256), losses := [] }

theorem u8602 : Upper (D 7) (R 7) [36,192,65,18,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8603 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 26 400 40 65 162 290), lower := (rows 37 194 69 26 400 40 65 128 256), losses := [] }

theorem u8603 : Upper (D 7) (R 7) [36,192,65,18,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8603 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8604 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 194 69 26 400 40 66 161 289), lower := (rows 37 194 69 26 400 40 66 128 256), losses := [] }

theorem u8604 : Upper (D 7) (R 7) [36,192,65,18,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8604 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8605 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 26 400 40 96 131 259), lower := (rows 37 194 69 26 400 40 96 128 256), losses := [] }

theorem u8605 : Upper (D 7) (R 7) [36,192,65,18,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8605 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8606 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 69, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 194 69 42 145 288 66 152 280), lower := (rows 37 194 69 42 145 288 66 128 256), losses := [] }

theorem u8606 : Upper (D 7) (R 7) [36,192,65,34,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8606 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8607 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7)], upper := (rows 37 194 69 42 145 288 72 146 274), lower := (rows 37 194 69 42 145 288 72 128 256), losses := [] }

theorem u8607 : Upper (D 7) (R 7) [36,192,65,34,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8607 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8608 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 69 42 145 288 80 138 266), lower := (rows 37 194 69 42 145 288 80 128 256), losses := [] }

theorem u8608 : Upper (D 7) (R 7) [36,192,65,34,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8608 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8609 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 42 152 288 65 146 274), lower := (rows 37 194 69 42 152 288 65 128 256), losses := [] }

theorem u8609 : Upper (D 7) (R 7) [36,192,65,34,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8609 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8610 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 194 69 42 152 288 66 145 273), lower := (rows 37 194 69 42 152 288 66 128 256), losses := [] }

theorem u8610 : Upper (D 7) (R 7) [36,192,65,34,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8610 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8611 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 69 42 152 288 80 131 259), lower := (rows 37 194 69 42 152 288 80 128 256), losses := [] }

theorem u8611 : Upper (D 7) (R 7) [36,192,65,34,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8611 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8612 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 42 280 48 65 130 386), lower := (rows 37 194 69 42 280 48 65 128 256), losses := [] }

theorem u8612 : Upper (D 7) (R 7) [36,192,65,34,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8612 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8613 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(2,5)], upper := (rows 37 194 69 42 280 48 66 129 385), lower := (rows 37 194 69 42 280 48 66 128 256), losses := [] }

theorem u8613 : Upper (D 7) (R 7) [36,192,65,34,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8613 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8614 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 69 42 280 48 192 131 259), lower := (rows 37 194 69 42 280 48 192 128 256), losses := [] }

theorem u8614 : Upper (D 7) (R 7) [36,192,65,34,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8614 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8615 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 42 400 48 65 138 266), lower := (rows 37 194 69 42 400 48 65 128 256), losses := [] }

theorem u8615 : Upper (D 7) (R 7) [36,192,65,34,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8615 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8616 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 69, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 194 69 42 400 48 66 137 265), lower := (rows 37 194 69 42 400 48 66 128 256), losses := [] }

theorem u8616 : Upper (D 7) (R 7) [36,192,65,34,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8616 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8617 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 402, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 37 194 69 42 400 48 72 131 259), lower := (rows 37 194 69 42 400 48 72 128 256), losses := [] }

theorem u8617 : Upper (D 7) (R 7) [36,192,65,34,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8617 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8618 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 56 400 34 65 138 266), lower := (rows 37 194 69 56 400 34 65 128 256), losses := [] }

theorem u8618 : Upper (D 7) (R 7) [36,192,65,48,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8619 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 69 56 400 34 66 137 265), lower := (rows 37 194 69 56 400 34 66 128 256), losses := [] }

theorem u8619 : Upper (D 7) (R 7) [36,192,65,48,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8620 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 56 400 34 72 131 259), lower := (rows 37 194 69 56 400 34 72 128 256), losses := [] }

theorem u8620 : Upper (D 7) (R 7) [36,192,65,48,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8620 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8621 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 37 194 69 137 274 48 66 168 296), lower := (rows 37 194 69 137 274 48 66 128 256), losses := [] }

theorem u8621 : Upper (D 7) (R 7) [36,192,65,129,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8621 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8622 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 69 137 274 48 72 162 290), lower := (rows 37 194 69 137 274 48 72 128 256), losses := [] }

theorem u8622 : Upper (D 7) (R 7) [36,192,65,129,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8622 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8623 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 137 274 48 96 138 266), lower := (rows 37 194 69 137 274 48 96 128 256), losses := [] }

theorem u8623 : Upper (D 7) (R 7) [36,192,65,129,258,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8623 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8624 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 194 69 137 280 48 66 162 290), lower := (rows 37 194 69 137 280 48 66 128 256), losses := [] }

theorem u8624 : Upper (D 7) (R 7) [36,192,65,129,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8624 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8625 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 137 280 48 96 130 258), lower := (rows 37 194 69 137 280 48 96 128 256), losses := [] }

theorem u8625 : Upper (D 7) (R 7) [36,192,65,129,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8625 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8626 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 69 152 273 40 66 162 290), lower := (rows 37 194 69 152 273 40 66 128 256), losses := [] }

theorem u8626 : Upper (D 7) (R 7) [36,192,65,144,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8626 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8627 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 152 273 40 96 130 258), lower := (rows 37 194 69 152 273 40 96 128 256), losses := [] }

theorem u8627 : Upper (D 7) (R 7) [36,192,65,144,257,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8627 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8628 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 152 274 34 65 168 296), lower := (rows 37 194 69 152 274 34 65 128 256), losses := [] }

theorem u8628 : Upper (D 7) (R 7) [36,192,65,144,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8629 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 194 69 152 274 34 72 161 289), lower := (rows 37 194 69 152 274 34 72 128 256), losses := [] }

theorem u8629 : Upper (D 7) (R 7) [36,192,65,144,258,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8629 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8630 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 69 152 274 34 96 137 265), lower := (rows 37 194 69 152 274 34 96 128 256), losses := [] }

theorem u8630 : Upper (D 7) (R 7) [36,192,65,144,258,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8631 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 152 274 40 65 162 290), lower := (rows 37 194 69 152 274 40 65 128 256), losses := [] }

theorem u8631 : Upper (D 7) (R 7) [36,192,65,144,258,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8631 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8632 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 37 194 69 152 274 40 66 161 289), lower := (rows 37 194 69 152 274 40 66 128 256), losses := [{ target := 5, region := (rows 1 138 5 8 16 0 250 128 256), good := (rows 69 194 69 218 338 74 66 194 256) }] }

theorem u8632 : Upper (D 7) (R 7) [36,192,65,144,258,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8632 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8633 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 69 152 274 40 96 131 259), lower := (rows 37 194 69 152 274 40 96 128 256), losses := [] }

theorem u8633 : Upper (D 7) (R 7) [36,192,65,144,258,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8633 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8634 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 152 280 34 65 162 290), lower := (rows 37 194 69 152 280 34 65 128 256), losses := [] }

theorem u8634 : Upper (D 7) (R 7) [36,192,65,144,264,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8635 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 69 152 280 34 66 161 289), lower := (rows 37 194 69 152 280 34 66 128 256), losses := [] }

theorem u8635 : Upper (D 7) (R 7) [36,192,65,144,264,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8636 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 69 152 280 34 96 131 259), lower := (rows 37 194 69 152 280 34 96 128 256), losses := [] }

theorem u8636 : Upper (D 7) (R 7) [36,192,65,144,264,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8637 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 194 69 152 304 34 65 138 266), lower := (rows 37 194 69 152 304 34 65 128 256), losses := [] }

theorem u8637 : Upper (D 7) (R 7) [36,192,65,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8638 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 69 152 304 34 66 137 265), lower := (rows 37 194 69 152 304 34 66 128 256), losses := [] }

theorem u8638 : Upper (D 7) (R 7) [36,192,65,144,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8639 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 194 69 152 304 34 72 131 259), lower := (rows 37 194 69 152 304 34 72 128 256), losses := [] }

theorem u8639 : Upper (D 7) (R 7) [36,192,65,144,288,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8639 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8639
end Delivery.IrregularNine14.P07
