import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0009

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7560 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 25 84 288 68 131 259), lower := (rows 35 194 44 25 84 288 68 128 256), losses := [] }

theorem u7560 : Upper (D 6) (R 6) [34,192,40,17,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7560 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7561 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 28 81 288 65 134 262), lower := (rows 35 194 44 28 81 288 65 128 256), losses := [] }

theorem u7561 : Upper (D 6) (R 6) [34,192,40,20,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7561 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7562 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 300, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 194 44 28 81 288 66 133 261), lower := (rows 35 194 44 28 81 288 66 128 256), losses := [] }

theorem u7562 : Upper (D 6) (R 6) [34,192,40,20,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7562 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7563 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 28 81 288 68 131 259), lower := (rows 35 194 44 28 81 288 68 128 256), losses := [] }

theorem u7563 : Upper (D 6) (R 6) [34,192,40,20,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7563 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7564 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 44 28 336 33 65 134 262), lower := (rows 35 194 44 28 336 33 65 128 256), losses := [] }

theorem u7564 : Upper (D 6) (R 6) [34,192,40,20,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7565 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 44 28 336 33 66 133 261), lower := (rows 35 194 44 28 336 33 66 128 256), losses := [] }

theorem u7565 : Upper (D 6) (R 6) [34,192,40,20,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7566 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 44 28 336 33 68 131 259), lower := (rows 35 194 44 28 336 33 68 128 256), losses := [] }

theorem u7566 : Upper (D 6) (R 6) [34,192,40,20,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7567 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 194 44 73 22 288 65 148 276), lower := (rows 35 194 44 73 22 288 65 128 256), losses := [] }

theorem u7567 : Upper (D 6) (R 6) [34,192,40,65,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7567 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7568 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 73 22 288 68 145 273), lower := (rows 35 194 44 73 22 288 68 128 256), losses := [] }

theorem u7568 : Upper (D 6) (R 6) [34,192,40,65,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7568 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7569 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 292, targets := 2 }], pairs := [(2,1)], upper := (rows 35 194 44 73 22 288 80 133 261), lower := (rows 35 194 44 73 22 288 80 128 256), losses := [] }

theorem u7569 : Upper (D 6) (R 6) [34,192,40,65,6,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7569 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7570 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 194 44 73 276 48 65 134 262), lower := (rows 35 194 44 73 276 48 65 128 256), losses := [] }

theorem u7570 : Upper (D 6) (R 6) [34,192,40,65,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7570 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7571 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 308, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 194 44 73 276 48 66 133 261), lower := (rows 35 194 44 73 276 48 66 128 256), losses := [] }

theorem u7571 : Upper (D 6) (R 6) [34,192,40,65,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7571 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7572 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 73 276 48 68 131 259), lower := (rows 35 194 44 73 276 48 68 128 256), losses := [] }

theorem u7572 : Upper (D 6) (R 6) [34,192,40,65,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7572 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7573 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 194 44 76 273 33 66 148 276), lower := (rows 35 194 44 76 273 33 66 128 256), losses := [] }

theorem u7573 : Upper (D 6) (R 6) [34,192,40,68,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7574 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 44 76 273 33 68 146 274), lower := (rows 35 194 44 76 273 33 68 128 256), losses := [] }

theorem u7574 : Upper (D 6) (R 6) [34,192,40,68,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7575 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 44 76 273 33 80 134 262), lower := (rows 35 194 44 76 273 33 80 128 256), losses := [] }

theorem u7575 : Upper (D 6) (R 6) [34,192,40,68,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7575 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7576 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 76 273 48 65 134 262), lower := (rows 35 194 44 76 273 48 65 128 256), losses := [] }

theorem u7576 : Upper (D 6) (R 6) [34,192,40,68,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7576 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7577 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 44 76 273 48 66 133 261), lower := (rows 35 194 44 76 273 48 66 128 256), losses := [] }

theorem u7577 : Upper (D 6) (R 6) [34,192,40,68,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7577 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7578 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 44 76 273 48 68 131 259), lower := (rows 35 194 44 76 273 48 68 128 256), losses := [] }

theorem u7578 : Upper (D 6) (R 6) [34,192,40,68,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7578 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7579 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 76 274 33 65 148 276), lower := (rows 35 194 44 76 274 33 65 128 256), losses := [] }

theorem u7579 : Upper (D 6) (R 6) [34,192,40,68,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7580 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 44 76 274 33 68 145 273), lower := (rows 35 194 44 76 274 33 68 128 256), losses := [] }

theorem u7580 : Upper (D 6) (R 6) [34,192,40,68,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7581 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 44 76 274 33 80 133 261), lower := (rows 35 194 44 76 274 33 80 128 256), losses := [] }

theorem u7581 : Upper (D 6) (R 6) [34,192,40,68,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7581 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7582 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 44 88 276 33 65 134 262), lower := (rows 35 194 44 88 276 33 65 128 256), losses := [] }

theorem u7582 : Upper (D 6) (R 6) [34,192,40,80,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7583 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 44 88 276 33 66 133 261), lower := (rows 35 194 44 88 276 33 66 128 256), losses := [] }

theorem u7583 : Upper (D 6) (R 6) [34,192,40,80,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7584 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 44 88 276 33 68 131 259), lower := (rows 35 194 44 88 276 33 68 128 256), losses := [] }

theorem u7584 : Upper (D 6) (R 6) [34,192,40,80,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7585 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 44 280 84 33 65 134 262), lower := (rows 35 194 44 280 84 33 65 128 256), losses := [] }

theorem u7585 : Upper (D 6) (R 6) [34,192,40,272,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7586 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 44 280 84 33 66 133 261), lower := (rows 35 194 44 280 84 33 66 128 256), losses := [] }

theorem u7586 : Upper (D 6) (R 6) [34,192,40,272,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7587 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 194 44 280 84 33 68 131 259), lower := (rows 35 194 44 280 84 33 68 128 256), losses := [] }

theorem u7587 : Upper (D 6) (R 6) [34,192,40,272,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7588 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 44 328 22 33 65 148 276), lower := (rows 35 194 44 328 22 33 65 128 256), losses := [] }

theorem u7588 : Upper (D 6) (R 6) [34,192,40,320,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7589 : Route 9 := (fun mask => (mask,id))

def c7589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7589 : Upper (D 6) (R 6) [34,192,40,320,6,1,4] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,6,1,4] 13 (by decide) (choices 1) [1,16] r7589 c7589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u579
  · exact u580

def b7590 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 44 328 22 33 80 133 261), lower := (rows 35 194 44 328 22 33 80 128 256), losses := [] }

theorem u7590 : Upper (D 6) (R 6) [34,192,40,320,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7590 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7591 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 76 13 273 48 66 164 292), lower := (rows 35 194 76 13 273 48 66 128 256), losses := [] }

theorem u7591 : Upper (D 6) (R 6) [34,192,72,5,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7591 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7592 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 76, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 35 194 76 13 273 48 68 162 290), lower := (rows 35 194 76 13 273 48 68 128 256), losses := [] }

theorem u7592 : Upper (D 6) (R 6) [34,192,72,5,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7592 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7593 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 76 13 273 48 96 134 262), lower := (rows 35 194 76 13 273 48 96 128 256), losses := [] }

theorem u7593 : Upper (D 6) (R 6) [34,192,72,5,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7593 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7594 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 76 13 274 33 68 176 304), lower := (rows 35 194 76 13 274 33 68 128 256), losses := [] }

theorem u7594 : Upper (D 6) (R 6) [34,192,72,5,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7595 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 76 13 274 33 80 164 292), lower := (rows 35 194 76 13 274 33 80 128 256), losses := [] }

theorem u7595 : Upper (D 6) (R 6) [34,192,72,5,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7595 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7596 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 76 13 274 33 96 148 276), lower := (rows 35 194 76 13 274 33 96 128 256), losses := [] }

theorem u7596 : Upper (D 6) (R 6) [34,192,72,5,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7597 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 32 },{ cop := 3, region := 304, targets := 2 }], pairs := [(2,5),(3,5),(4,1)], upper := (rows 35 194 76 13 304 33 66 148 276), lower := (rows 35 194 76 13 304 33 66 128 256), losses := [] }

theorem u7597 : Upper (D 6) (R 6) [34,192,72,5,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7598 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 76 13 304 33 68 146 274), lower := (rows 35 194 76 13 304 33 68 128 256), losses := [] }

theorem u7598 : Upper (D 6) (R 6) [34,192,72,5,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7599 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 76 13 304 33 80 134 262), lower := (rows 35 194 76 13 304 33 80 128 256), losses := [] }

theorem u7599 : Upper (D 6) (R 6) [34,192,72,5,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7599 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7600 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 3, region := 68, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 35 194 76 25 274 36 65 164 292), lower := (rows 35 194 76 25 274 36 65 128 256), losses := [] }

theorem u7600 : Upper (D 6) (R 6) [34,192,72,17,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7601 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 25 274 36 68 161 289), lower := (rows 35 194 76 25 274 36 68 128 256), losses := [] }

theorem u7601 : Upper (D 6) (R 6) [34,192,72,17,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7602 : Route 9 := (fun mask => (mask,id))

def c7602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7602 : Upper (D 6) (R 6) [34,192,72,17,258,4,32] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17,258,4,32] 13 (by decide) (choices 1) [1,4] r7602 c7602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u581
  · exact u582

def b7603 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 76 25 276 33 66 164 292), lower := (rows 35 194 76 25 276 33 66 128 256), losses := [] }

theorem u7603 : Upper (D 6) (R 6) [34,192,72,17,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7604 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 194 76 25 276 33 68 162 290), lower := (rows 35 194 76 25 276 33 68 128 256), losses := [] }

theorem u7604 : Upper (D 6) (R 6) [34,192,72,17,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7605 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 76 25 276 33 96 134 262), lower := (rows 35 194 76 25 276 33 96 128 256), losses := [] }

theorem u7605 : Upper (D 6) (R 6) [34,192,72,17,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7606 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 35 194 76 25 276 36 65 162 290), lower := (rows 35 194 76 25 276 36 65 128 256), losses := [] }

theorem u7606 : Upper (D 6) (R 6) [34,192,72,17,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7607 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 76 25 276 36 66 161 289), lower := (rows 35 194 76 25 276 36 66 128 256), losses := [] }

theorem u7607 : Upper (D 6) (R 6) [34,192,72,17,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7608 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 194 76 25 276 36 96 131 259), lower := (rows 35 194 76 25 276 36 96 128 256), losses := [] }

theorem u7608 : Upper (D 6) (R 6) [34,192,72,17,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7609 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 76 25 304 36 65 134 262), lower := (rows 35 194 76 25 304 36 65 128 256), losses := [] }

theorem u7609 : Upper (D 6) (R 6) [34,192,72,17,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7610 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 76 25 304 36 66 133 261), lower := (rows 35 194 76 25 304 36 66 128 256), losses := [] }

theorem u7610 : Upper (D 6) (R 6) [34,192,72,17,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7611 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 25 304 36 68 131 259), lower := (rows 35 194 76 25 304 36 68 128 256), losses := [] }

theorem u7611 : Upper (D 6) (R 6) [34,192,72,17,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7612 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 35 194 76 26 273 36 65 164 292), lower := (rows 35 194 76 26 273 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 44 81 172 300), good := (rows 497 192 492 508 337 420 81 128 256) }] }

theorem u7612 : Upper (D 6) (R 6) [34,192,72,18,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7613 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 26 273 36 68 161 289), lower := (rows 35 194 76 26 273 36 68 128 256), losses := [] }

theorem u7613 : Upper (D 6) (R 6) [34,192,72,18,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7614 : Route 9 := (fun mask => (mask,id))

def c7614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7614 : Upper (D 6) (R 6) [34,192,72,18,257,4,32] 13 := by
  apply FastRouting.sound _ _ [34,192,72,18,257,4,32] 13 (by decide) (choices 1) [1,4] r7614 c7614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u583
  · exact u584

def r7615 : Route 9 := (fun mask => (mask,id))

def c7615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7615 : Upper (D 6) (R 6) [34,192,72,18,288,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,18,288,4,1] 13 (by decide) (choices 1) [1,4] r7615 c7615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u585
  · exact u586

def b7616 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 26 304 36 68 129 257), lower := (rows 35 194 76 26 304 36 68 128 256), losses := [] }

theorem u7616 : Upper (D 6) (R 6) [34,192,72,18,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7617 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 76 28 273 33 66 164 292), lower := (rows 35 194 76 28 273 33 66 128 256), losses := [] }

theorem u7617 : Upper (D 6) (R 6) [34,192,72,20,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7618 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 76 28 273 33 68 162 290), lower := (rows 35 194 76 28 273 33 68 128 256), losses := [] }

theorem u7618 : Upper (D 6) (R 6) [34,192,72,20,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7619 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 },{ cop := 4, region := 108, targets := 2 }], pairs := [(1,0),(1,5),(2,1)], upper := (rows 35 194 76 28 273 33 96 134 262), lower := (rows 35 194 76 28 273 33 96 128 256), losses := [] }

theorem u7619 : Upper (D 6) (R 6) [34,192,72,20,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7619
end Delivery.IrregularNine14.P06
