import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006
import IrregularNine14P06C0007

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5640 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 134 41 336 36 68 131 259), lower := (rows 25 98 134 41 336 36 68 128 256), losses := [] }

theorem u5640 : Upper (D 6) (R 6) [24,96,130,33,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5641 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 25 98 134 44 84 33 320 131 259), lower := (rows 25 98 134 44 84 33 320 128 256), losses := [] }

theorem u5641 : Upper (D 6) (R 6) [24,96,130,36,68,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5641 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5642 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5)], upper := (rows 25 98 134 44 84 34 320 129 257), lower := (rows 25 98 134 44 84 34 320 128 256), losses := [] }

theorem u5642 : Upper (D 6) (R 6) [24,96,130,36,68,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5642 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5643 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 98 134 44 274 33 65 196 324), lower := (rows 25 98 134 44 274 33 65 128 256), losses := [] }

theorem u5643 : Upper (D 6) (R 6) [24,96,130,36,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5644 : Route 9 := (fun mask => (mask,id))

def c5644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5644 : Upper (D 6) (R 6) [24,96,130,36,258,1,4] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,258,1,4] 13 (by decide) (choices 1) [1,64] r5644 c5644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u419
  · exact u420

def b5645 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 98 134 44 336 33 65 134 262), lower := (rows 25 98 134 44 336 33 65 128 256), losses := [] }

theorem u5645 : Upper (D 6) (R 6) [24,96,130,36,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5646 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(0,5),(1,0),(1,2)], upper := (rows 25 98 134 44 336 33 66 133 261), lower := (rows 25 98 134 44 336 33 66 128 256), losses := [{ target := 5, region := (rows 9 2 4 8 24 0 70 136 264), good := (rows 409 66 198 477 336 1 66 128 256) }] }

theorem u5646 : Upper (D 6) (R 6) [24,96,130,36,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5647 : Route 9 := (fun mask => (mask,id))

def c5647 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5647 : Upper (D 6) (R 6) [24,96,130,36,320,1,4] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,320,1,4] 13 (by decide) (choices 1) [1,2] r5647 c5647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u421
  · exact u422

def b5648 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 98 164 11 84 288 65 134 262), lower := (rows 25 98 164 11 84 288 65 128 256), losses := [] }

theorem u5648 : Upper (D 6) (R 6) [24,96,160,3,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5648 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5649 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 420, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 25 98 164 11 84 288 66 133 261), lower := (rows 25 98 164 11 84 288 66 128 256), losses := [] }

theorem u5649 : Upper (D 6) (R 6) [24,96,160,3,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5649 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5650 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 25 98 164 11 84 288 68 131 259), lower := (rows 25 98 164 11 84 288 68 128 256), losses := [] }

theorem u5650 : Upper (D 6) (R 6) [24,96,160,3,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5650 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5651 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 164 11 276 34 65 196 324), lower := (rows 25 98 164 11 276 34 65 128 256), losses := [] }

theorem u5651 : Upper (D 6) (R 6) [24,96,160,3,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5652 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 34, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 164 11 276 34 68 193 321), lower := (rows 25 98 164 11 276 34 68 128 256), losses := [] }

theorem u5652 : Upper (D 6) (R 6) [24,96,160,3,260,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5653 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 164 13 274 34 65 196 324), lower := (rows 25 98 164 13 274 34 65 128 256), losses := [] }

theorem u5653 : Upper (D 6) (R 6) [24,96,160,5,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5654 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 34, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 164 13 274 34 68 193 321), lower := (rows 25 98 164 13 274 34 68 128 256), losses := [] }

theorem u5654 : Upper (D 6) (R 6) [24,96,160,5,258,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5655 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 164 13 336 34 65 134 262), lower := (rows 25 98 164 13 336 34 65 128 256), losses := [] }

theorem u5655 : Upper (D 6) (R 6) [24,96,160,5,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5656 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 25 98 164 13 336 34 66 133 261), lower := (rows 25 98 164 13 336 34 66 128 256), losses := [] }

theorem u5656 : Upper (D 6) (R 6) [24,96,160,5,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5657 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 164 13 336 34 68 131 259), lower := (rows 25 98 164 13 336 34 68 128 256), losses := [] }

theorem u5657 : Upper (D 6) (R 6) [24,96,160,5,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5658 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 98 164 14 336 33 65 134 262), lower := (rows 25 98 164 14 336 33 65 128 256), losses := [] }

theorem u5658 : Upper (D 6) (R 6) [24,96,160,6,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5659 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 25 98 164 14 336 33 66 133 261), lower := (rows 25 98 164 14 336 33 66 128 256), losses := [] }

theorem u5659 : Upper (D 6) (R 6) [24,96,160,6,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5660 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 74, targets := 1 },{ cop := 3, region := 337, targets := 32 }], pairs := [(0,5),(1,0),(3,0)], upper := (rows 25 98 164 14 336 33 68 131 259), lower := (rows 25 98 164 14 336 33 68 128 256), losses := [] }

theorem u5660 : Upper (D 6) (R 6) [24,96,160,6,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5661 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 25 98 164 73 276 34 65 134 262), lower := (rows 25 98 164 73 276 34 65 128 256), losses := [] }

theorem u5661 : Upper (D 6) (R 6) [24,96,160,65,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5662 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 25 98 164 73 276 34 66 133 261), lower := (rows 25 98 164 73 276 34 66 128 256), losses := [] }

theorem u5662 : Upper (D 6) (R 6) [24,96,160,65,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5663 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 73, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 98 164 73 276 34 68 131 259), lower := (rows 25 98 164 73 276 34 68 128 256), losses := [] }

theorem u5663 : Upper (D 6) (R 6) [24,96,160,65,260,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5664 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 174, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 98 164 76 273 34 65 134 262), lower := (rows 25 98 164 76 273 34 65 128 256), losses := [] }

theorem u5664 : Upper (D 6) (R 6) [24,96,160,68,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5665 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 273, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 164 76 273 34 66 133 261), lower := (rows 25 98 164 76 273 34 66 128 256), losses := [] }

theorem u5665 : Upper (D 6) (R 6) [24,96,160,68,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5666 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 25 98 164 76 273 34 68 131 259), lower := (rows 25 98 164 76 273 34 68 128 256), losses := [] }

theorem u5666 : Upper (D 6) (R 6) [24,96,160,68,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5667 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 98 164 76 274 33 65 134 262), lower := (rows 25 98 164 76 274 33 65 128 256), losses := [] }

theorem u5667 : Upper (D 6) (R 6) [24,96,160,68,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5668 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 25 98 164 76 274 33 66 133 261), lower := (rows 25 98 164 76 274 33 66 128 256), losses := [] }

theorem u5668 : Upper (D 6) (R 6) [24,96,160,68,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5669 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 25 98 164 76 274 33 68 131 259), lower := (rows 25 98 164 76 274 33 68 128 256), losses := [] }

theorem u5669 : Upper (D 6) (R 6) [24,96,160,68,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5670 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 98 164 76 276 33 65 130 258), lower := (rows 25 98 164 76 276 33 65 128 256), losses := [] }

theorem u5670 : Upper (D 6) (R 6) [24,96,160,68,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5671 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 74, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 25 98 164 76 276 33 66 131 259), lower := (rows 25 98 164 76 276 33 66 128 256), losses := [] }

theorem u5671 : Upper (D 6) (R 6) [24,96,160,68,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5672 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 73, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 98 164 76 276 34 65 131 259), lower := (rows 25 98 164 76 276 34 65 128 256), losses := [] }

theorem u5672 : Upper (D 6) (R 6) [24,96,160,68,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5673 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 273, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 164 76 276 34 66 129 257), lower := (rows 25 98 164 76 276 34 66 128 256), losses := [] }

theorem u5673 : Upper (D 6) (R 6) [24,96,160,68,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5674 : Route 9 := (fun mask => (mask,id))

def c5674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5674 : Upper (D 6) (R 6) [24,129,257,6,34,64,4] 13 := by
  apply FastRouting.sound _ _ [24,129,257,6,34,64,4] 13 (by decide) (choices 1) [32,64] r5674 c5674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u423
  · exact u424

def b5675 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(4,0),(4,2)], upper := (rows 25 131 261 14 50 96 96 196 324), lower := (rows 25 131 261 14 50 96 96 128 256), losses := [] }

theorem u5675 : Upper (D 6) (R 6) [24,129,257,6,34,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5676 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 25 131 261 14 112 34 68 224 352), lower := (rows 25 131 261 14 112 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 48 32 79 176 304), good := (rows 477 197 325 76 496 496 68 128 256) }] }

theorem u5676 : Upper (D 6) (R 6) [24,129,257,6,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5677 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 25 131 261 14 112 34 96 196 324), lower := (rows 25 131 261 14 112 34 96 128 256), losses := [] }

theorem u5677 : Upper (D 6) (R 6) [24,129,257,6,96,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5678 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 104, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 25 131 261 42 52 96 66 196 324), lower := (rows 25 131 261 42 52 96 66 128 256), losses := [] }

theorem u5678 : Upper (D 6) (R 6) [24,129,257,34,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5679 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 25 131 261 42 82 36 68 224 352), lower := (rows 25 131 261 42 82 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 100 100 252 380), good := (rows 408 130 484 506 506 484 484 128 256) }] }

theorem u5679 : Upper (D 6) (R 6) [24,129,257,34,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5680 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 81, targets := 4 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 25 131 261 42 82 36 96 196 324), lower := (rows 25 131 261 42 82 36 96 128 256), losses := [] }

theorem u5680 : Upper (D 6) (R 6) [24,129,257,34,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5681 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 25 131 261 42 84 34 96 196 324), lower := (rows 25 131 261 42 84 34 96 128 256), losses := [] }

theorem u5681 : Upper (D 6) (R 6) [24,129,257,34,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5682 : Route 9 := (fun mask => (mask,id))

def c5682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5682 : Upper (D 6) (R 6) [24,129,257,34,68,4,2] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,68,4,2] 13 (by decide) (choices 1) [32,64] r5682 c5682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u425
  · exact u426

def b5683 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(0,1),(4,0),(4,1)], upper := (rows 25 131 261 42 84 36 96 194 322), lower := (rows 25 131 261 42 84 36 96 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 52 52 125 128 256), good := (rows 121 193 373 121 116 116 112 128 256) }] }

theorem u5683 : Upper (D 6) (R 6) [24,129,257,34,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5684 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 25 131 261 42 84 96 96 134 262), lower := (rows 25 131 261 42 84 96 96 128 256), losses := [] }

theorem u5684 : Upper (D 6) (R 6) [24,129,257,34,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5685 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 3, region := 81, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 25 131 261 42 112 36 66 196 324), lower := (rows 25 131 261 42 112 36 66 128 256), losses := [] }

theorem u5685 : Upper (D 6) (R 6) [24,129,257,34,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5686 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 131 261 42 112 36 68 194 322), lower := (rows 25 131 261 42 112 36 68 128 256), losses := [] }

theorem u5686 : Upper (D 6) (R 6) [24,129,257,34,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5687 : Route 9 := (fun mask => (mask,id))

def c5687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5687 : Upper (D 6) (R 6) [24,129,258,5,34,64,4] 13 := by
  apply FastRouting.sound _ _ [24,129,258,5,34,64,4] 13 (by decide) (choices 1) [32,64] r5687 c5687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u427
  · exact u428

def b5688 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 1, region := 112, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 131 262 13 50 96 96 196 324), lower := (rows 25 131 262 13 50 96 96 128 256), losses := [] }

theorem u5688 : Upper (D 6) (R 6) [24,129,258,5,34,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5689 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 25 131 262 13 112 34 68 224 352), lower := (rows 25 131 262 13 112 34 68 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 80 47 64 208 336), good := (rows 443 163 290 43 496 34 496 128 256) }] }

theorem u5689 : Upper (D 6) (R 6) [24,129,258,5,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5690 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 25 131 262 13 112 34 96 196 324), lower := (rows 25 131 262 13 112 34 96 128 256), losses := [] }

theorem u5690 : Upper (D 6) (R 6) [24,129,258,5,96,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5691 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 25 131 262 13 112 36 96 194 322), lower := (rows 25 131 262 13 112 36 96 128 256), losses := [] }

theorem u5691 : Upper (D 6) (R 6) [24,129,258,5,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5692 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 80, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 25 131 262 41 82 36 68 224 352), lower := (rows 25 131 262 41 82 36 68 128 256), losses := [] }

theorem u5692 : Upper (D 6) (R 6) [24,129,258,33,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5693 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 260, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 131 262 41 82 36 96 196 324), lower := (rows 25 131 262 41 82 36 96 128 256), losses := [] }

theorem u5693 : Upper (D 6) (R 6) [24,129,258,33,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5694 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 104, targets := 4 }], pairs := [(1,5),(2,5),(3,2)], upper := (rows 25 131 262 42 52 96 65 196 324), lower := (rows 25 131 262 42 52 96 65 128 256), losses := [] }

theorem u5694 : Upper (D 6) (R 6) [24,129,258,34,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5695 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 104, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 25 131 262 42 52 96 68 193 321), lower := (rows 25 131 262 42 52 96 68 128 256), losses := [] }

theorem u5695 : Upper (D 6) (R 6) [24,129,258,34,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5696 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 260, targets := 65 },{ cop := 1, region := 104, targets := 4 }], pairs := [(2,0),(2,6),(3,2)], upper := (rows 25 131 262 42 84 96 65 164 292), lower := (rows 25 131 262 42 84 96 65 128 256), losses := [] }

theorem u5696 : Upper (D 6) (R 6) [24,129,258,34,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5697 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 131 262 42 84 96 68 161 289), lower := (rows 25 131 262 42 84 96 68 128 256), losses := [] }

theorem u5697 : Upper (D 6) (R 6) [24,129,258,34,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5698 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 25 131 262 42 84 96 96 133 261), lower := (rows 25 131 262 42 84 96 96 128 256), losses := [] }

theorem u5698 : Upper (D 6) (R 6) [24,129,258,34,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5699 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 301, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 25 131 292 13 82 96 66 164 292), lower := (rows 25 131 292 13 82 96 66 128 256), losses := [] }

theorem u5699 : Upper (D 6) (R 6) [24,129,288,5,66,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5699
end Delivery.IrregularNine14.P06
