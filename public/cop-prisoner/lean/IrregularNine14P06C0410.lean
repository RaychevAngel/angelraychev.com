import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0126

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24600 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 44 88 274 33 69 133 261), lower := (rows 35 194 44 88 274 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 136 264), good := (rows 35 163 428 445 307 33 0 128 256) }] }

theorem u24600 : Upper (D 6) (R 6) [34,192,40,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24601 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 88 274 36 69 133 261), lower := (rows 35 194 44 88 274 36 64 128 256), losses := [] }

theorem u24601 : Upper (D 6) (R 6) [34,192,40,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24602 : Route 9 := (fun mask => (mask,id))

def c24602 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24602 : Upper (D 6) (R 6) [34,192,40,80,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80,260,1] 13 (by decide) (choices 1) [1,2,4] r24602 c24602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7582
  · exact u7583
  · exact u7584

def b24603 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 88 276 34 69 133 261), lower := (rows 35 194 44 88 276 34 64 128 256), losses := [] }

theorem u24603 : Upper (D 6) (R 6) [34,192,40,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24604 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 88 276 36 67 131 259), lower := (rows 35 194 44 88 276 36 64 128 256), losses := [] }

theorem u24604 : Upper (D 6) (R 6) [34,192,40,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24605 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 265 22 33 84 212 340), lower := (rows 35 194 44 265 22 33 64 128 256), losses := [] }

theorem u24605 : Upper (D 6) (R 6) [34,192,40,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24606 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 265 22 36 81 209 337), lower := (rows 35 194 44 265 22 36 64 128 256), losses := [] }

theorem u24606 : Upper (D 6) (R 6) [34,192,40,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24607 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 265 22 48 69 197 325), lower := (rows 35 194 44 265 22 48 64 128 256), losses := [] }

theorem u24607 : Upper (D 6) (R 6) [34,192,40,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24607 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24608 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 265 22 96 85 149 277), lower := (rows 35 194 44 265 22 96 64 128 256), losses := [] }

theorem u24608 : Upper (D 6) (R 6) [34,192,40,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24609 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 265 81 34 84 148 276), lower := (rows 35 194 44 265 81 34 64 128 256), losses := [] }

theorem u24609 : Upper (D 6) (R 6) [34,192,40,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24610 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 265 81 36 86 150 278), lower := (rows 35 194 44 265 81 36 64 128 256), losses := [] }

theorem u24610 : Upper (D 6) (R 6) [34,192,40,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24611 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 44 265 81 48 70 134 262), lower := (rows 35 194 44 265 81 48 64 128 256), losses := [] }

theorem u24611 : Upper (D 6) (R 6) [34,192,40,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24611 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24612 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 265 84 33 86 150 278), lower := (rows 35 194 44 265 84 33 64 128 256), losses := [] }

theorem u24612 : Upper (D 6) (R 6) [34,192,40,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24613 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 265 84 34 85 149 277), lower := (rows 35 194 44 265 84 34 64 128 256), losses := [] }

theorem u24613 : Upper (D 6) (R 6) [34,192,40,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24614 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 265 84 36 83 147 275), lower := (rows 35 194 44 265 84 36 64 128 256), losses := [] }

theorem u24614 : Upper (D 6) (R 6) [34,192,40,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24615 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 44 265 84 48 71 135 263), lower := (rows 35 194 44 265 84 48 64 128 256), losses := [] }

theorem u24615 : Upper (D 6) (R 6) [34,192,40,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24615 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24616 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 44 266 21 33 84 212 340), lower := (rows 35 194 44 266 21 33 64 128 256), losses := [] }

theorem u24616 : Upper (D 6) (R 6) [34,192,40,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24617 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 194 44 266 21 36 81 209 337), lower := (rows 35 194 44 266 21 36 64 128 256), losses := [] }

theorem u24617 : Upper (D 6) (R 6) [34,192,40,258,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24618 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 44 266 21 48 69 197 325), lower := (rows 35 194 44 266 21 48 64 128 256), losses := [] }

theorem u24618 : Upper (D 6) (R 6) [34,192,40,258,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24618 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24619 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 266 21 96 85 149 277), lower := (rows 35 194 44 266 21 96 64 128 256), losses := [] }

theorem u24619 : Upper (D 6) (R 6) [34,192,40,258,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24620 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 44 266 81 33 84 148 276), lower := (rows 35 194 44 266 81 33 64 128 256), losses := [] }

theorem u24620 : Upper (D 6) (R 6) [34,192,40,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24621 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 194 44 266 81 36 85 149 277), lower := (rows 35 194 44 266 81 36 64 128 256), losses := [] }

theorem u24621 : Upper (D 6) (R 6) [34,192,40,258,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24622 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 44 266 81 48 69 133 261), lower := (rows 35 194 44 266 81 48 64 128 256), losses := [] }

theorem u24622 : Upper (D 6) (R 6) [34,192,40,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24622 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24623 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 44 266 84 33 85 149 277), lower := (rows 35 194 44 266 84 33 64 128 256), losses := [] }

theorem u24623 : Upper (D 6) (R 6) [34,192,40,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24624 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 194 44 266 84 36 81 145 273), lower := (rows 35 194 44 266 84 36 64 128 256), losses := [] }

theorem u24624 : Upper (D 6) (R 6) [34,192,40,258,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24625 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 44 266 84 48 69 133 261), lower := (rows 35 194 44 266 84 48 64 128 256), losses := [] }

theorem u24625 : Upper (D 6) (R 6) [34,192,40,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24625 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24626 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 44 268 22 33 81 209 337), lower := (rows 35 194 44 268 22 33 64 128 256), losses := [] }

theorem u24626 : Upper (D 6) (R 6) [34,192,40,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24627 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 268 22 48 65 193 321), lower := (rows 35 194 44 268 22 48 64 128 256), losses := [] }

theorem u24627 : Upper (D 6) (R 6) [34,192,40,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24627 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24628 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 268 22 96 81 145 273), lower := (rows 35 194 44 268 22 96 64 128 256), losses := [] }

theorem u24628 : Upper (D 6) (R 6) [34,192,40,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24629 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 44 268 81 33 86 150 278), lower := (rows 35 194 44 268 81 33 64 128 256), losses := [] }

theorem u24629 : Upper (D 6) (R 6) [34,192,40,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24630 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 268 81 34 85 149 277), lower := (rows 35 194 44 268 81 34 64 128 256), losses := [] }

theorem u24630 : Upper (D 6) (R 6) [34,192,40,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24631 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 268 81 36 83 147 275), lower := (rows 35 194 44 268 81 36 64 128 256), losses := [] }

theorem u24631 : Upper (D 6) (R 6) [34,192,40,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24632 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 44 268 81 48 71 135 263), lower := (rows 35 194 44 268 81 48 64 128 256), losses := [] }

theorem u24632 : Upper (D 6) (R 6) [34,192,40,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24632 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24633 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 44 268 84 33 83 147 275), lower := (rows 35 194 44 268 84 33 64 128 256), losses := [] }

theorem u24633 : Upper (D 6) (R 6) [34,192,40,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24634 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 268 84 34 81 145 273), lower := (rows 35 194 44 268 84 34 64 128 256), losses := [] }

theorem u24634 : Upper (D 6) (R 6) [34,192,40,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24635 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 194 44 268 84 48 67 131 259), lower := (rows 35 194 44 268 84 48 64 128 256), losses := [] }

theorem u24635 : Upper (D 6) (R 6) [34,192,40,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24635 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24636 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 44 280 21 33 70 198 326), lower := (rows 35 194 44 280 21 33 64 128 256), losses := [] }

theorem u24636 : Upper (D 6) (R 6) [34,192,40,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24637 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 280 21 34 69 197 325), lower := (rows 35 194 44 280 21 34 64 128 256), losses := [] }

theorem u24637 : Upper (D 6) (R 6) [34,192,40,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24638 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 194 44 280 21 36 67 195 323), lower := (rows 35 194 44 280 21 36 64 128 256), losses := [] }

theorem u24638 : Upper (D 6) (R 6) [34,192,40,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24639 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 280 21 96 71 135 263), lower := (rows 35 194 44 280 21 96 64 128 256), losses := [] }

theorem u24639 : Upper (D 6) (R 6) [34,192,40,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24640 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 44 280 22 33 69 197 325), lower := (rows 35 194 44 280 22 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 128 256), good := (rows 35 163 44 317 55 33 0 128 256) }] }

theorem u24640 : Upper (D 6) (R 6) [34,192,40,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24641 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 280 22 36 65 193 321), lower := (rows 35 194 44 280 22 36 64 128 256), losses := [] }

theorem u24641 : Upper (D 6) (R 6) [34,192,40,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24642 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 280 22 96 69 133 261), lower := (rows 35 194 44 280 22 96 64 128 256), losses := [] }

theorem u24642 : Upper (D 6) (R 6) [34,192,40,272,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24643 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 2, region := 194, targets := 1 }], pairs := [(0,2),(1,0),(4,2)], upper := (rows 35 194 44 280 81 33 70 134 262), lower := (rows 35 194 44 280 81 33 64 128 256), losses := [] }

theorem u24643 : Upper (D 6) (R 6) [34,192,40,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24644 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 280 81 34 69 133 261), lower := (rows 35 194 44 280 81 34 64 128 256), losses := [] }

theorem u24644 : Upper (D 6) (R 6) [34,192,40,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24645 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 280 81 36 71 135 263), lower := (rows 35 194 44 280 81 36 64 128 256), losses := [] }

theorem u24645 : Upper (D 6) (R 6) [34,192,40,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24646 : Route 9 := (fun mask => (mask,id))

def c24646 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24646 : Upper (D 6) (R 6) [34,192,40,272,68,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,68,1] 13 (by decide) (choices 1) [1,2,4] r24646 c24646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7585
  · exact u7586
  · exact u7587

def b24647 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 280 84 34 69 133 261), lower := (rows 35 194 44 280 84 34 64 128 256), losses := [] }

theorem u24647 : Upper (D 6) (R 6) [34,192,40,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24648 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 280 84 36 67 131 259), lower := (rows 35 194 44 280 84 36 64 128 256), losses := [] }

theorem u24648 : Upper (D 6) (R 6) [34,192,40,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24649 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 44 328 21 33 86 150 278), lower := (rows 35 194 44 328 21 33 64 128 256), losses := [] }

theorem u24649 : Upper (D 6) (R 6) [34,192,40,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24650 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 328 21 34 85 149 277), lower := (rows 35 194 44 328 21 34 64 128 256), losses := [] }

theorem u24650 : Upper (D 6) (R 6) [34,192,40,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24651 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 194 44 328 21 36 83 147 275), lower := (rows 35 194 44 328 21 36 64 128 256), losses := [] }

theorem u24651 : Upper (D 6) (R 6) [34,192,40,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24652 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 194 44 328 21 48 71 135 263), lower := (rows 35 194 44 328 21 48 64 128 256), losses := [] }

theorem u24652 : Upper (D 6) (R 6) [34,192,40,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24652 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24653 : Route 9 := (fun mask => (mask,id))

def c24653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24653 : Upper (D 6) (R 6) [34,192,40,320,6,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,6,1] 13 (by decide) (choices 1) [1,4,16] r24653 c24653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7588
  · exact u7589
  · exact u7590

def b24654 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 328 22 36 81 145 273), lower := (rows 35 194 44 328 22 36 64 128 256), losses := [] }

theorem u24654 : Upper (D 6) (R 6) [34,192,40,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24655 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 328 22 48 69 133 261), lower := (rows 35 194 44 328 22 48 64 128 256), losses := [] }

theorem u24655 : Upper (D 6) (R 6) [34,192,40,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24655 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24656 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 48, targets := 2 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 194 76 13 52 33 338 402 274), lower := (rows 35 194 76 13 52 33 64 128 256), losses := [] }

theorem u24656 : Upper (D 6) (R 6) [34,192,72,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24657 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 13 52 34 337 401 273), lower := (rows 35 194 76 13 52 34 64 128 256), losses := [] }

theorem u24657 : Upper (D 6) (R 6) [34,192,72,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24658 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 76 13 52 48 323 387 259), lower := (rows 35 194 76 13 52 48 64 128 256), losses := [] }

theorem u24658 : Upper (D 6) (R 6) [34,192,72,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24658 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24659 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 195, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 194 76 13 52 288 83 147 275), lower := (rows 35 194 76 13 52 288 64 128 256), losses := [] }

theorem u24659 : Upper (D 6) (R 6) [34,192,72,5,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24659 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24659
end Delivery.IrregularNine14.P06
