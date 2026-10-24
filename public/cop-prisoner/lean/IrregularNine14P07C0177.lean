import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10620 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 138, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 162 70 137 276 48 72 131 259), lower := (rows 97 162 70 137 276 48 72 128 256), losses := [] }

theorem u10620 : Upper (D 7) (R 7) [96,160,66,129,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10620 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10621 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 162 70 140 273 33 66 152 280), lower := (rows 97 162 70 140 273 33 66 128 256), losses := [] }

theorem u10621 : Upper (D 7) (R 7) [96,160,66,132,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10622 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 162 70 140 273 33 72 146 274), lower := (rows 97 162 70 140 273 33 72 128 256), losses := [] }

theorem u10622 : Upper (D 7) (R 7) [96,160,66,132,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10622 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10623 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 162 70 140 273 33 80 138 266), lower := (rows 97 162 70 140 273 33 80 128 256), losses := [] }

theorem u10623 : Upper (D 7) (R 7) [96,160,66,132,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10623 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10624 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 162 70 140 273 48 65 138 266), lower := (rows 97 162 70 140 273 48 65 128 256), losses := [] }

theorem u10624 : Upper (D 7) (R 7) [96,160,66,132,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10624 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10625 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 162 70 140 273 48 66 137 265), lower := (rows 97 162 70 140 273 48 66 128 256), losses := [] }

theorem u10625 : Upper (D 7) (R 7) [96,160,66,132,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10625 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10626 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 76, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 97 162 70 140 273 48 72 131 259), lower := (rows 97 162 70 140 273 48 72 128 256), losses := [] }

theorem u10626 : Upper (D 7) (R 7) [96,160,66,132,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10626 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10627 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 408, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 162 70 140 274 33 65 152 280), lower := (rows 97 162 70 140 274 33 65 128 256), losses := [] }

theorem u10627 : Upper (D 7) (R 7) [96,160,66,132,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10628 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 162 70 140 274 33 72 145 273), lower := (rows 97 162 70 140 274 33 72 128 256), losses := [] }

theorem u10628 : Upper (D 7) (R 7) [96,160,66,132,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10628 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10629 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1)], upper := (rows 97 162 70 140 274 33 80 137 265), lower := (rows 97 162 70 140 274 33 80 128 256), losses := [] }

theorem u10629 : Upper (D 7) (R 7) [96,160,66,132,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10629 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10630 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(2,7)], upper := (rows 97 162 70 140 274 48 65 137 265), lower := (rows 97 162 70 140 274 48 65 128 256), losses := [] }

theorem u10630 : Upper (D 7) (R 7) [96,160,66,132,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10630 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10631 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 76, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 97 162 70 140 274 48 72 129 257), lower := (rows 97 162 70 140 274 48 72 128 256), losses := [] }

theorem u10631 : Upper (D 7) (R 7) [96,160,66,132,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10631 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10632 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 408, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 162 70 140 280 33 65 146 274), lower := (rows 97 162 70 140 280 33 65 128 256), losses := [] }

theorem u10632 : Upper (D 7) (R 7) [96,160,66,132,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10633 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 162 70 140 280 33 66 145 273), lower := (rows 97 162 70 140 280 33 66 128 256), losses := [] }

theorem u10633 : Upper (D 7) (R 7) [96,160,66,132,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10634 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 97, targets := 130 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,1),(0,7),(1,6)], upper := (rows 97 162 70 140 280 33 80 131 259), lower := (rows 97 162 70 140 280 33 80 128 256), losses := [] }

theorem u10634 : Upper (D 7) (R 7) [96,160,66,132,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10634 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10635 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 97 162 70 152 273 33 66 140 268), lower := (rows 97 162 70 152 273 33 66 128 256), losses := [] }

theorem u10635 : Upper (D 7) (R 7) [96,160,66,144,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10636 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 70 152 273 33 68 138 266), lower := (rows 97 162 70 152 273 33 68 128 256), losses := [] }

theorem u10636 : Upper (D 7) (R 7) [96,160,66,144,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10636 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10637 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 134, targets := 1 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(2,0)], upper := (rows 97 162 70 152 273 33 72 134 262), lower := (rows 97 162 70 152 273 33 72 128 256), losses := [] }

theorem u10637 : Upper (D 7) (R 7) [96,160,66,144,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10637 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10638 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 97 162 70 152 273 34 65 140 268), lower := (rows 97 162 70 152 273 34 65 128 256), losses := [] }

theorem u10638 : Upper (D 7) (R 7) [96,160,66,144,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10639 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 162 70 152 273 34 68 137 265), lower := (rows 97 162 70 152 273 34 68 128 256), losses := [] }

theorem u10639 : Upper (D 7) (R 7) [96,160,66,144,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10639 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10640 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 305, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(4,7)], upper := (rows 97 162 70 152 273 34 72 133 261), lower := (rows 97 162 70 152 273 34 72 128 256), losses := [] }

theorem u10640 : Upper (D 7) (R 7) [96,160,66,144,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10640 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10641 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 408, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 162 70 152 274 33 65 140 268), lower := (rows 97 162 70 152 274 33 65 128 256), losses := [] }

theorem u10641 : Upper (D 7) (R 7) [96,160,66,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10642 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 70 152 274 33 68 137 265), lower := (rows 97 162 70 152 274 33 68 128 256), losses := [] }

theorem u10642 : Upper (D 7) (R 7) [96,160,66,144,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10642 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10643 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 305, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(4,7)], upper := (rows 97 162 70 152 274 33 72 133 261), lower := (rows 97 162 70 152 274 33 72 128 256), losses := [] }

theorem u10643 : Upper (D 7) (R 7) [96,160,66,144,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10643 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10644 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 408, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 162 70 152 276 33 65 138 266), lower := (rows 97 162 70 152 276 33 65 128 256), losses := [] }

theorem u10644 : Upper (D 7) (R 7) [96,160,66,144,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10645 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 97 162 70 152 276 33 66 137 265), lower := (rows 97 162 70 152 276 33 66 128 256), losses := [] }

theorem u10645 : Upper (D 7) (R 7) [96,160,66,144,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10646 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 305, targets := 128 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,7),(1,6),(4,7)], upper := (rows 97 162 70 152 276 33 72 131 259), lower := (rows 97 162 70 152 276 33 72 128 256), losses := [] }

theorem u10646 : Upper (D 7) (R 7) [96,160,66,144,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10646 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10647 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 97 162 70 152 276 34 65 137 265), lower := (rows 97 162 70 152 276 34 65 128 256), losses := [] }

theorem u10647 : Upper (D 7) (R 7) [96,160,66,144,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10648 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 305, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(4,7)], upper := (rows 97 162 70 152 276 34 72 129 257), lower := (rows 97 162 70 152 276 34 72 128 256), losses := [] }

theorem u10648 : Upper (D 7) (R 7) [96,160,66,144,260,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10648 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10649 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 408, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 162 70 152 280 33 65 134 262), lower := (rows 97 162 70 152 280 33 65 128 256), losses := [] }

theorem u10649 : Upper (D 7) (R 7) [96,160,66,144,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10650 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 97 162 70 152 280 33 66 133 261), lower := (rows 97 162 70 152 280 33 66 128 256), losses := [] }

theorem u10650 : Upper (D 7) (R 7) [96,160,66,144,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10651 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 70 152 280 33 68 131 259), lower := (rows 97 162 70 152 280 33 68 128 256), losses := [] }

theorem u10651 : Upper (D 7) (R 7) [96,160,66,144,264,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10651 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10652 : Route 9 := (fun mask => (mask,id))

def c10652 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10652 : Upper (D 7) (R 7) [96,160,72,144,257,1,2] 13 := by
  apply FastRouting.sound _ _ [96,160,72,144,257,1,2] 13 (by decide) (choices 1) [2,4] r10652 c10652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u797
  · exact u798

def b10653 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 76 152 273 33 68 130 258), lower := (rows 97 162 76 152 273 33 68 128 256), losses := [] }

theorem u10653 : Upper (D 7) (R 7) [96,160,72,144,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10653 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10654 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 162, targets := 65 },{ cop := 5, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 162 76 152 273 34 65 134 262), lower := (rows 97 162 76 152 273 34 65 128 256), losses := [] }

theorem u10654 : Upper (D 7) (R 7) [96,160,72,144,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10655 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 76 152 273 34 66 133 261), lower := (rows 97 162 76 152 273 34 66 128 256), losses := [] }

theorem u10655 : Upper (D 7) (R 7) [96,160,72,144,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10656 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 76 152 273 34 68 131 259), lower := (rows 97 162 76 152 273 34 68 128 256), losses := [] }

theorem u10656 : Upper (D 7) (R 7) [96,160,72,144,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10656 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10657 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 162 76 152 274 33 65 134 262), lower := (rows 97 162 76 152 274 33 65 128 256), losses := [] }

theorem u10657 : Upper (D 7) (R 7) [96,160,72,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10658 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(2,0),(2,5)], upper := (rows 97 162 76 152 274 33 66 133 261), lower := (rows 97 162 76 152 274 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 82 128 256), good := (rows 96 226 76 220 338 32 66 128 256) },{ target := 5, region := (rows 1 2 12 8 16 0 82 128 256), good := (rows 65 194 76 220 338 1 66 128 256) }] }

theorem u10658 : Upper (D 7) (R 7) [96,160,72,144,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10659 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 76 152 274 33 68 131 259), lower := (rows 97 162 76 152 274 33 68 128 256), losses := [] }

theorem u10659 : Upper (D 7) (R 7) [96,160,72,144,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10659 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10660 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 162 76 152 276 33 65 130 258), lower := (rows 97 162 76 152 276 33 65 128 256), losses := [] }

theorem u10660 : Upper (D 7) (R 7) [96,160,72,144,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10661 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(4,7)], upper := (rows 97 162 76 152 276 33 66 131 259), lower := (rows 97 162 76 152 276 33 66 128 256), losses := [{ target := 7, region := (rows 71 2 4 8 20 119 66 0 322), good := (rows 353 355 381 56 309 33 355 0 256) }] }

theorem u10661 : Upper (D 7) (R 7) [96,160,72,144,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10662 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 1, region := 65, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 162 76 152 276 34 65 131 259), lower := (rows 97 162 76 152 276 34 65 128 256), losses := [] }

theorem u10662 : Upper (D 7) (R 7) [96,160,72,144,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10663 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 76 152 276 34 66 129 257), lower := (rows 97 162 76 152 276 34 66 128 256), losses := [] }

theorem u10663 : Upper (D 7) (R 7) [96,160,72,144,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10664 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 386, targets := 32 },{ cop := 6, region := 161, targets := 2 }], pairs := [(0,1),(1,5),(4,0),(4,1)], upper := (rows 97 259 13 26 52 160 66 192 448), lower := (rows 97 259 13 26 52 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 255 74 207 335), good := (rows 480 482 508 506 436 160 482 160 256) },{ target := 1, region := (rows 65 0 4 8 20 231 64 193 321), good := (rows 481 417 445 56 52 160 481 160 256) }] }

theorem u10664 : Upper (D 7) (R 7) [96,257,9,18,36,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10665 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 259 13 26 52 160 192 194 322), lower := (rows 97 259 13 26 52 160 192 128 256), losses := [] }

theorem u10665 : Upper (D 7) (R 7) [96,257,9,18,36,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10666 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 259 13 26 148 34 96 192 448), lower := (rows 97 259 13 26 148 34 96 128 256), losses := [] }

theorem u10666 : Upper (D 7) (R 7) [96,257,9,18,132,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10667 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 291, targets := 128 },{ cop := 5, region := 193, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,0)], upper := (rows 97 259 13 26 148 34 192 224 352), lower := (rows 97 259 13 26 148 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 42 255 175 303), good := (rows 480 482 508 506 468 482 192 192 256) }] }

theorem u10667 : Upper (D 7) (R 7) [96,257,9,18,132,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10668 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(4,0)], upper := (rows 97 259 13 26 176 34 68 192 448), lower := (rows 97 259 13 26 176 34 68 128 256), losses := [] }

theorem u10668 : Upper (D 7) (R 7) [96,257,9,18,160,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10668 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10669 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 450, targets := 32 },{ cop := 4, region := 65, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(4,0)], upper := (rows 97 259 13 26 176 34 192 196 324), lower := (rows 97 259 13 26 176 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 42 212 132 260), good := (rows 96 290 508 122 240 34 192 192 256) },{ target := 1, region := (rows 17 0 12 8 16 32 220 140 268), good := (rows 97 257 461 477 241 32 192 192 256) }] }

theorem u10669 : Upper (D 7) (R 7) [96,257,9,18,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10670 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(4,0)], upper := (rows 97 259 13 26 176 36 66 192 448), lower := (rows 97 259 13 26 176 36 66 128 256), losses := [] }

theorem u10670 : Upper (D 7) (R 7) [96,257,9,18,160,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10670 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10671 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 258, targets := 32 },{ cop := 0, region := 258, targets := 128 },{ cop := 4, region := 65, targets := 2 }], pairs := [(0,1),(1,5),(1,7)], upper := (rows 97 259 13 26 176 36 192 194 322), lower := (rows 97 259 13 26 176 36 192 128 256), losses := [] }

theorem u10671 : Upper (D 7) (R 7) [96,257,9,18,160,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10671 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10672 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 97 259 13 28 50 160 66 192 448), lower := (rows 97 259 13 28 50 160 66 128 256), losses := [] }

theorem u10672 : Upper (D 7) (R 7) [96,257,9,20,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10673 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 259 13 28 50 160 192 194 322), lower := (rows 97 259 13 28 50 160 192 128 256), losses := [] }

theorem u10673 : Upper (D 7) (R 7) [96,257,9,20,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10674 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 259 13 28 146 34 96 192 448), lower := (rows 97 259 13 28 146 34 96 128 256), losses := [] }

theorem u10674 : Upper (D 7) (R 7) [96,257,9,20,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10675 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 291, targets := 128 },{ cop := 1, region := 240, targets := 1 },{ cop := 5, region := 193, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,0)], upper := (rows 97 259 13 28 146 34 192 224 352), lower := (rows 97 259 13 28 146 34 192 128 256), losses := [] }

theorem u10675 : Upper (D 7) (R 7) [96,257,9,20,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10676 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 28 146 96 192 162 290), lower := (rows 97 259 13 28 146 96 192 128 256), losses := [] }

theorem u10676 : Upper (D 7) (R 7) [96,257,9,20,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10677 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 13 28 176 34 66 192 448), lower := (rows 97 259 13 28 176 34 66 128 256), losses := [] }

theorem u10677 : Upper (D 7) (R 7) [96,257,9,20,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10678 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 259 13 28 176 34 192 194 322), lower := (rows 97 259 13 28 176 34 192 128 256), losses := [] }

theorem u10678 : Upper (D 7) (R 7) [96,257,9,20,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10679 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 259 13 42 82 160 68 144 400), lower := (rows 97 259 13 42 82 160 68 128 256), losses := [] }

theorem u10679 : Upper (D 7) (R 7) [96,257,9,34,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10679 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10679
end Delivery.IrregularNine14.P07
