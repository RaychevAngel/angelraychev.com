import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0009
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7680 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 100 25 276 33 72 134 262), lower := (rows 35 194 100 25 276 33 72 128 256), losses := [] }

theorem u7680 : Upper (D 6) (R 6) [34,192,96,17,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7680 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7681 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 100 25 276 40 65 134 262), lower := (rows 35 194 100 25 276 40 65 128 256), losses := [] }

theorem u7681 : Upper (D 6) (R 6) [34,192,96,17,260,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7681 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7682 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 100 25 276 40 66 133 261), lower := (rows 35 194 100 25 276 40 66 128 256), losses := [] }

theorem u7682 : Upper (D 6) (R 6) [34,192,96,17,260,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7682 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7683 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 131, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 194 100 25 276 40 68 131 259), lower := (rows 35 194 100 25 276 40 68 128 256), losses := [] }

theorem u7683 : Upper (D 6) (R 6) [34,192,96,17,260,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7683 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7684 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 166, targets := 1 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 35 194 100 25 280 36 65 134 262), lower := (rows 35 194 100 25 280 36 65 128 256), losses := [] }

theorem u7684 : Upper (D 6) (R 6) [34,192,96,17,264,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7685 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 7, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 35 194 100 25 280 36 66 133 261), lower := (rows 35 194 100 25 280 36 66 128 256), losses := [] }

theorem u7685 : Upper (D 6) (R 6) [34,192,96,17,264,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7686 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 25 280 36 68 131 259), lower := (rows 35 194 100 25 280 36 68 128 256), losses := [] }

theorem u7686 : Upper (D 6) (R 6) [34,192,96,17,264,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7687 : Route 9 := (fun mask => (mask,id))

def c7687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7687 : Upper (D 6) (R 6) [34,192,96,18,257,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18,257,4,1] 13 (by decide) (choices 1) [4,8] r7687 c7687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u599
  · exact u600

def b7688 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 26 273 36 68 137 265), lower := (rows 35 194 100 26 273 36 68 128 256), losses := [] }

theorem u7688 : Upper (D 6) (R 6) [34,192,96,18,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7689 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 100 26 273 36 72 133 261), lower := (rows 35 194 100 26 273 36 72 128 256), losses := [] }

theorem u7689 : Upper (D 6) (R 6) [34,192,96,18,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7689 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7690 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 100 26 276 33 65 140 268), lower := (rows 35 194 100 26 276 33 65 128 256), losses := [] }

theorem u7690 : Upper (D 6) (R 6) [34,192,96,18,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7691 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 194 100 26 276 33 68 137 265), lower := (rows 35 194 100 26 276 33 68 128 256), losses := [] }

theorem u7691 : Upper (D 6) (R 6) [34,192,96,18,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7692 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 100 26 276 33 72 133 261), lower := (rows 35 194 100 26 276 33 72 128 256), losses := [] }

theorem u7692 : Upper (D 6) (R 6) [34,192,96,18,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7692 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7693 : Route 9 := (fun mask => (mask,id))

def c7693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7693 : Upper (D 6) (R 6) [34,192,96,18,264,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18,264,4,1] 13 (by decide) (choices 1) [1,4] r7693 c7693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u601
  · exact u602

def b7694 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 26 280 36 68 129 257), lower := (rows 35 194 100 26 280 36 68 128 256), losses := [] }

theorem u7694 : Upper (D 6) (R 6) [34,192,96,18,264,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7695 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 35 194 100 28 273 36 65 138 266), lower := (rows 35 194 100 28 273 36 65 128 256), losses := [] }

theorem u7695 : Upper (D 6) (R 6) [34,192,96,20,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7696 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 7, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 35 194 100 28 273 36 66 137 265), lower := (rows 35 194 100 28 273 36 66 128 256), losses := [] }

theorem u7696 : Upper (D 6) (R 6) [34,192,96,20,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7697 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 100 28 273 36 72 131 259), lower := (rows 35 194 100 28 273 36 72 128 256), losses := [] }

theorem u7697 : Upper (D 6) (R 6) [34,192,96,20,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7697 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7698 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 100 28 273 40 65 134 262), lower := (rows 35 194 100 28 273 40 65 128 256), losses := [] }

theorem u7698 : Upper (D 6) (R 6) [34,192,96,20,257,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7698 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7699 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 100 28 273 40 66 133 261), lower := (rows 35 194 100 28 273 40 66 128 256), losses := [] }

theorem u7699 : Upper (D 6) (R 6) [34,192,96,20,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7699 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7700 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 100 28 273 40 68 131 259), lower := (rows 35 194 100 28 273 40 68 128 256), losses := [] }

theorem u7700 : Upper (D 6) (R 6) [34,192,96,20,257,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7700 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7701 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 100 28 274 33 65 140 268), lower := (rows 35 194 100 28 274 33 65 128 256), losses := [] }

theorem u7701 : Upper (D 6) (R 6) [34,192,96,20,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7702 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 194 100 28 274 33 68 137 265), lower := (rows 35 194 100 28 274 33 68 128 256), losses := [] }

theorem u7702 : Upper (D 6) (R 6) [34,192,96,20,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7703 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 194 100 28 274 33 72 133 261), lower := (rows 35 194 100 28 274 33 72 128 256), losses := [] }

theorem u7703 : Upper (D 6) (R 6) [34,192,96,20,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7703 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7704 : Route 9 := (fun mask => (mask,id))

def c7704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7704 : Upper (D 6) (R 6) [34,192,96,20,258,8,1] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20,258,8,1] 13 (by decide) (choices 1) [1,4] r7704 c7704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u603
  · exact u604

def b7705 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 194 100 28 274 40 68 129 257), lower := (rows 35 194 100 28 274 40 68 128 256), losses := [] }

theorem u7705 : Upper (D 6) (R 6) [34,192,96,20,258,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7705 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7706 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 100 28 280 33 65 134 262), lower := (rows 35 194 100 28 280 33 65 128 256), losses := [] }

theorem u7706 : Upper (D 6) (R 6) [34,192,96,20,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7707 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 100 28 280 33 66 133 261), lower := (rows 35 194 100 28 280 33 66 128 256), losses := [] }

theorem u7707 : Upper (D 6) (R 6) [34,192,96,20,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7708 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 194 100 28 280 33 68 131 259), lower := (rows 35 194 100 28 280 33 68 128 256), losses := [] }

theorem u7708 : Upper (D 6) (R 6) [34,192,96,20,264,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7709 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 194 261 14 81 36 72 176 304), lower := (rows 35 194 261 14 81 36 72 128 256), losses := [] }

theorem u7709 : Upper (D 6) (R 6) [34,192,257,6,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7709 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7710 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 194 261 14 81 36 80 168 296), lower := (rows 35 194 261 14 81 36 80 128 256), losses := [] }

theorem u7710 : Upper (D 6) (R 6) [34,192,257,6,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7710 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7711 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 261 14 81 36 96 152 280), lower := (rows 35 194 261 14 81 36 96 128 256), losses := [] }

theorem u7711 : Upper (D 6) (R 6) [34,192,257,6,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7712 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(4,1)], upper := (rows 35 194 261 14 88 36 65 176 304), lower := (rows 35 194 261 14 88 36 65 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 44 64 144 272), good := (rows 34 194 292 46 506 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 24 44 69 152 280), good := (rows 97 192 357 508 504 100 65 128 256) }] }

theorem u7712 : Upper (D 6) (R 6) [34,192,257,6,72,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7713 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 261 14 88 36 80 161 289), lower := (rows 35 194 261 14 88 36 80 128 256), losses := [] }

theorem u7713 : Upper (D 6) (R 6) [34,192,257,6,72,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7713 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7714 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 194 261 14 88 36 96 145 273), lower := (rows 35 194 261 14 88 36 96 128 256), losses := [] }

theorem u7714 : Upper (D 6) (R 6) [34,192,257,6,72,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7715 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 194 261 14 112 36 65 152 280), lower := (rows 35 194 261 14 112 36 65 128 256), losses := [] }

theorem u7715 : Upper (D 6) (R 6) [34,192,257,6,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7716 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 194 261 14 112 36 72 145 273), lower := (rows 35 194 261 14 112 36 72 128 256), losses := [] }

theorem u7716 : Upper (D 6) (R 6) [34,192,257,6,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7716 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7717 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 301, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 261 14 112 36 80 137 265), lower := (rows 35 194 261 14 112 36 80 128 256), losses := [] }

theorem u7717 : Upper (D 6) (R 6) [34,192,257,6,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7717 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7718 : PairBound 9 := { available := 40, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 261 25 84 36 66 168 296), lower := (rows 35 194 261 25 84 36 66 128 256), losses := [] }

theorem u7718 : Upper (D 6) (R 6) [34,192,257,17,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7719 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 261 25 84 36 72 162 290), lower := (rows 35 194 261 25 84 36 72 128 256), losses := [] }

theorem u7719 : Upper (D 6) (R 6) [34,192,257,17,68,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7719 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7720 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 2, region := 112, targets := 1 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 35 194 261 25 84 36 96 138 266), lower := (rows 35 194 261 25 84 36 96 128 256), losses := [] }

theorem u7720 : Upper (D 6) (R 6) [34,192,257,17,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7721 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 261 25 84 40 66 164 292), lower := (rows 35 194 261 25 84 40 66 128 256), losses := [] }

theorem u7721 : Upper (D 6) (R 6) [34,192,257,17,68,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7721 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7722 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 194 261 25 84 40 68 162 290), lower := (rows 35 194 261 25 84 40 68 128 256), losses := [] }

theorem u7722 : Upper (D 6) (R 6) [34,192,257,17,68,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7722 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7723 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 260, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 194 261 25 84 40 96 134 262), lower := (rows 35 194 261 25 84 40 96 128 256), losses := [] }

theorem u7723 : Upper (D 6) (R 6) [34,192,257,17,68,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7723 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7724 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 261 25 112 36 66 140 268), lower := (rows 35 194 261 25 112 36 66 128 256), losses := [] }

theorem u7724 : Upper (D 6) (R 6) [34,192,257,17,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7725 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 194 261 25 112 36 68 138 266), lower := (rows 35 194 261 25 112 36 68 128 256), losses := [] }

theorem u7725 : Upper (D 6) (R 6) [34,192,257,17,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7726 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 194 261 25 112 36 72 134 262), lower := (rows 35 194 261 25 112 36 72 128 256), losses := [] }

theorem u7726 : Upper (D 6) (R 6) [34,192,257,17,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7726 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7727 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 293, targets := 64 },{ cop := 2, region := 80, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 35 194 261 26 81 36 68 168 296), lower := (rows 35 194 261 26 81 36 68 128 256), losses := [] }

theorem u7727 : Upper (D 6) (R 6) [34,192,257,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7728 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 194 261 26 81 36 72 164 292), lower := (rows 35 194 261 26 81 36 72 128 256), losses := [] }

theorem u7728 : Upper (D 6) (R 6) [34,192,257,18,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7728 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7729 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 261 26 81 36 96 140 268), lower := (rows 35 194 261 26 81 36 96 128 256), losses := [] }

theorem u7729 : Upper (D 6) (R 6) [34,192,257,18,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7730 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 293, targets := 64 },{ cop := 4, region := 170, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 35 194 261 26 84 36 65 168 296), lower := (rows 35 194 261 26 84 36 65 128 256), losses := [] }

theorem u7730 : Upper (D 6) (R 6) [34,192,257,18,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7731 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 260, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 194 261 26 84 36 72 161 289), lower := (rows 35 194 261 26 84 36 72 128 256), losses := [] }

theorem u7731 : Upper (D 6) (R 6) [34,192,257,18,68,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7731 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7732 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 3, region := 293, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 194 261 26 84 36 96 137 265), lower := (rows 35 194 261 26 84 36 96 128 256), losses := [] }

theorem u7732 : Upper (D 6) (R 6) [34,192,257,18,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7733 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 293, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 194 261 26 112 36 65 140 268), lower := (rows 35 194 261 26 112 36 65 128 256), losses := [] }

theorem u7733 : Upper (D 6) (R 6) [34,192,257,18,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7734 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 194 261 26 112 36 68 137 265), lower := (rows 35 194 261 26 112 36 68 128 256), losses := [] }

theorem u7734 : Upper (D 6) (R 6) [34,192,257,18,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7735 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 194 261 26 112 36 72 133 261), lower := (rows 35 194 261 26 112 36 72 128 256), losses := [] }

theorem u7735 : Upper (D 6) (R 6) [34,192,257,18,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7735 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7736 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 300, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 194 261 28 81 36 66 168 296), lower := (rows 35 194 261 28 81 36 66 128 256), losses := [] }

theorem u7736 : Upper (D 6) (R 6) [34,192,257,20,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7737 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 261 28 81 36 72 162 290), lower := (rows 35 194 261 28 81 36 72 128 256), losses := [] }

theorem u7737 : Upper (D 6) (R 6) [34,192,257,20,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7737 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7738 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 261 28 81 36 96 138 266), lower := (rows 35 194 261 28 81 36 96 128 256), losses := [] }

theorem u7738 : Upper (D 6) (R 6) [34,192,257,20,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7739 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 120, targets := 2 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 35 194 261 28 112 36 65 138 266), lower := (rows 35 194 261 28 112 36 65 128 256), losses := [] }

theorem u7739 : Upper (D 6) (R 6) [34,192,257,20,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7739
end Delivery.IrregularNine14.P06
