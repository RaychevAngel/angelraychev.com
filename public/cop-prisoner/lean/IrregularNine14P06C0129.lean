import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7740 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 261 28 112 36 66 137 265), lower := (rows 35 194 261 28 112 36 66 128 256), losses := [] }

theorem u7740 : Upper (D 6) (R 6) [34,192,257,20,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7741 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 261 28 112 36 72 131 259), lower := (rows 35 194 261 28 112 36 72 128 256), losses := [] }

theorem u7741 : Upper (D 6) (R 6) [34,192,257,20,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7741 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7742 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 300, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 194 261 56 81 36 66 140 268), lower := (rows 35 194 261 56 81 36 66 128 256), losses := [] }

theorem u7742 : Upper (D 6) (R 6) [34,192,257,48,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7743 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 2, region := 80, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 35 194 261 56 81 36 68 138 266), lower := (rows 35 194 261 56 81 36 68 128 256), losses := [] }

theorem u7743 : Upper (D 6) (R 6) [34,192,257,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7744 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 194 261 56 81 36 72 134 262), lower := (rows 35 194 261 56 81 36 72 128 256), losses := [] }

theorem u7744 : Upper (D 6) (R 6) [34,192,257,48,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7744 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7745 : Route 9 := (fun mask => (mask,id))

def c7745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7745 : Upper (D 6) (R 6) [34,192,258,17,68,4,1] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17,68,4,1] 13 (by decide) (choices 1) [8,32] r7745 c7745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u605
  · exact u606

def b7746 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 262 25 84 36 72 161 289), lower := (rows 35 194 262 25 84 36 72 128 256), losses := [] }

theorem u7746 : Upper (D 6) (R 6) [34,192,258,17,68,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7746 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7747 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 194 262 25 84 36 96 137 265), lower := (rows 35 194 262 25 84 36 96 128 256), losses := [] }

theorem u7747 : Upper (D 6) (R 6) [34,192,258,17,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7748 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 260, targets := 1 },{ cop := 0, region := 260, targets := 64 }], pairs := [(2,0),(2,6)], upper := (rows 35 194 262 25 84 40 65 164 292), lower := (rows 35 194 262 25 84 40 65 128 256), losses := [] }

theorem u7748 : Upper (D 6) (R 6) [34,192,258,17,68,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7748 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7749 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 194 262 25 84 40 68 161 289), lower := (rows 35 194 262 25 84 40 68 128 256), losses := [] }

theorem u7749 : Upper (D 6) (R 6) [34,192,258,17,68,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7749 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7750 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 194 262 25 84 40 96 133 261), lower := (rows 35 194 262 25 84 40 96 128 256), losses := [] }

theorem u7750 : Upper (D 6) (R 6) [34,192,258,17,68,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7750 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7751 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 262 25 88 36 65 164 292), lower := (rows 35 194 262 25 88 36 65 128 256), losses := [] }

theorem u7751 : Upper (D 6) (R 6) [34,192,258,17,72,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7752 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 35 194 262 25 88 36 68 161 289), lower := (rows 35 194 262 25 88 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 100 100 129 257), good := (rows 505 224 356 409 120 100 100 128 256) }] }

theorem u7752 : Upper (D 6) (R 6) [34,192,258,17,72,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7753 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 194 262 25 88 36 96 133 261), lower := (rows 35 194 262 25 88 36 96 128 256), losses := [] }

theorem u7753 : Upper (D 6) (R 6) [34,192,258,17,72,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7754 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 194 262 28 81 36 65 168 296), lower := (rows 35 194 262 28 81 36 65 128 256), losses := [] }

theorem u7754 : Upper (D 6) (R 6) [34,192,258,20,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7755 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 262 28 81 36 72 161 289), lower := (rows 35 194 262 28 81 36 72 128 256), losses := [] }

theorem u7755 : Upper (D 6) (R 6) [34,192,258,20,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7755 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7756 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 262 28 81 36 96 137 265), lower := (rows 35 194 262 28 81 36 96 128 256), losses := [] }

theorem u7756 : Upper (D 6) (R 6) [34,192,258,20,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7757 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 194 262 28 112 36 65 137 265), lower := (rows 35 194 262 28 112 36 65 128 256), losses := [] }

theorem u7757 : Upper (D 6) (R 6) [34,192,258,20,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7758 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 262 28 112 36 72 129 257), lower := (rows 35 194 262 28 112 36 72 128 256), losses := [] }

theorem u7758 : Upper (D 6) (R 6) [34,192,258,20,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7758 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7759 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 194 262 56 81 36 65 140 268), lower := (rows 35 194 262 56 81 36 65 128 256), losses := [] }

theorem u7759 : Upper (D 6) (R 6) [34,192,258,48,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7760 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,0),(3,1)], upper := (rows 35 194 262 56 81 36 68 137 265), lower := (rows 35 194 262 56 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 100 128 256), good := (rows 98 226 358 120 120 100 100 128 256) },{ target := 1, region := (rows 1 0 4 25 17 100 100 145 273), good := (rows 505 224 356 504 505 100 100 128 256) }] }

theorem u7760 : Upper (D 6) (R 6) [34,192,258,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7761 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 194 262 56 81 36 72 133 261), lower := (rows 35 194 262 56 81 36 72 128 256), losses := [] }

theorem u7761 : Upper (D 6) (R 6) [34,192,258,48,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7761 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7762 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 292, targets := 66 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 35 194 268 25 84 33 66 164 292), lower := (rows 35 194 268 25 84 33 66 128 256), losses := [] }

theorem u7762 : Upper (D 6) (R 6) [34,192,264,17,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7763 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 194 268 25 84 33 68 162 290), lower := (rows 35 194 268 25 84 33 68 128 256), losses := [] }

theorem u7763 : Upper (D 6) (R 6) [34,192,264,17,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7764 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 130, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 268 25 84 33 96 134 262), lower := (rows 35 194 268 25 84 33 96 128 256), losses := [] }

theorem u7764 : Upper (D 6) (R 6) [34,192,264,17,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7765 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 194 268 25 112 36 65 134 262), lower := (rows 35 194 268 25 112 36 65 128 256), losses := [] }

theorem u7765 : Upper (D 6) (R 6) [34,192,264,17,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7766 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 268 25 112 36 66 133 261), lower := (rows 35 194 268 25 112 36 66 128 256), losses := [] }

theorem u7766 : Upper (D 6) (R 6) [34,192,264,17,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7767 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 194 268 25 112 36 68 131 259), lower := (rows 35 194 268 25 112 36 68 128 256), losses := [] }

theorem u7767 : Upper (D 6) (R 6) [34,192,264,17,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7768 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 194 268 26 81 36 65 164 292), lower := (rows 35 194 268 26 81 36 65 128 256), losses := [] }

theorem u7768 : Upper (D 6) (R 6) [34,192,264,18,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7769 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 293, targets := 64 }], pairs := [(0,6),(2,1),(2,6)], upper := (rows 35 194 268 26 81 36 68 161 289), lower := (rows 35 194 268 26 81 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 108 108 145 273), good := (rows 497 224 364 508 497 100 100 128 256) }] }

theorem u7769 : Upper (D 6) (R 6) [34,192,264,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7770 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 268 26 81 36 96 133 261), lower := (rows 35 194 268 26 81 36 96 128 256), losses := [] }

theorem u7770 : Upper (D 6) (R 6) [34,192,264,18,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7771 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 293, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 194 268 26 112 36 65 133 261), lower := (rows 35 194 268 26 112 36 65 128 256), losses := [] }

theorem u7771 : Upper (D 6) (R 6) [34,192,264,18,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7772 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 194 268 26 112 36 68 129 257), lower := (rows 35 194 268 26 112 36 68 128 256), losses := [] }

theorem u7772 : Upper (D 6) (R 6) [34,192,264,18,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7773 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 194 268 56 81 36 65 134 262), lower := (rows 35 194 268 56 81 36 65 128 256), losses := [] }

theorem u7773 : Upper (D 6) (R 6) [34,192,264,48,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7774 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 300, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 194 268 56 81 36 66 133 261), lower := (rows 35 194 268 56 81 36 66 128 256), losses := [] }

theorem u7774 : Upper (D 6) (R 6) [34,192,264,48,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7775 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 130, targets := 36 }], pairs := [(1,2),(1,5),(3,0)], upper := (rows 35 194 268 56 81 36 68 131 259), lower := (rows 35 194 268 56 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 100 128 256), good := (rows 98 226 364 120 120 100 100 128 256) }] }

theorem u7775 : Upper (D 6) (R 6) [34,192,264,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7776 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 130, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 268 56 84 33 65 134 262), lower := (rows 35 194 268 56 84 33 65 128 256), losses := [] }

theorem u7776 : Upper (D 6) (R 6) [34,192,264,48,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7777 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 268 56 84 33 66 133 261), lower := (rows 35 194 268 56 84 33 66 128 256), losses := [] }

theorem u7777 : Upper (D 6) (R 6) [34,192,264,48,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7778 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 194 268 56 84 33 68 131 259), lower := (rows 35 194 268 56 84 33 68 128 256), losses := [] }

theorem u7778 : Upper (D 6) (R 6) [34,192,264,48,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7779 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 308, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 194 268 73 21 36 66 176 304), lower := (rows 35 194 268 73 21 36 66 128 256), losses := [] }

theorem u7779 : Upper (D 6) (R 6) [34,192,264,65,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7780 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 194 268 73 21 36 80 162 290), lower := (rows 35 194 268 73 21 36 80 128 256), losses := [] }

theorem u7780 : Upper (D 6) (R 6) [34,192,264,65,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7780 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7781 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 194 268 73 21 36 96 146 274), lower := (rows 35 194 268 73 21 36 96 128 256), losses := [] }

theorem u7781 : Upper (D 6) (R 6) [34,192,264,65,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7782 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 308, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 194 268 73 21 48 66 164 292), lower := (rows 35 194 268 73 21 48 66 128 256), losses := [] }

theorem u7782 : Upper (D 6) (R 6) [34,192,264,65,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7782 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7783 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 226, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(3,1)], upper := (rows 35 194 268 73 21 48 68 162 290), lower := (rows 35 194 268 73 21 48 68 128 256), losses := [] }

theorem u7783 : Upper (D 6) (R 6) [34,192,264,65,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7783 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7784 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 268 73 21 48 96 134 262), lower := (rows 35 194 268 73 21 48 96 128 256), losses := [] }

theorem u7784 : Upper (D 6) (R 6) [34,192,264,65,5,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7784 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7785 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 194 268 73 22 36 65 176 304), lower := (rows 35 194 268 73 22 36 65 128 256), losses := [] }

theorem u7785 : Upper (D 6) (R 6) [34,192,264,65,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7786 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 194 268 73 22 36 80 161 289), lower := (rows 35 194 268 73 22 36 80 128 256), losses := [] }

theorem u7786 : Upper (D 6) (R 6) [34,192,264,65,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7786 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7787 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 194 268 73 22 36 96 145 273), lower := (rows 35 194 268 73 22 36 96 128 256), losses := [] }

theorem u7787 : Upper (D 6) (R 6) [34,192,264,65,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7788 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 268 88 21 33 66 164 292), lower := (rows 35 194 268 88 21 33 66 128 256), losses := [] }

theorem u7788 : Upper (D 6) (R 6) [34,192,264,80,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7789 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,2),(0,6),(3,0)], upper := (rows 35 194 268 88 21 33 68 162 290), lower := (rows 35 194 268 88 21 33 68 128 256), losses := [] }

theorem u7789 : Upper (D 6) (R 6) [34,192,264,80,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7790 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 268 88 21 33 96 134 262), lower := (rows 35 194 268 88 21 33 96 128 256), losses := [] }

theorem u7790 : Upper (D 6) (R 6) [34,192,264,80,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7791 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 268 88 52 33 65 134 262), lower := (rows 35 194 268 88 52 33 65 128 256), losses := [] }

theorem u7791 : Upper (D 6) (R 6) [34,192,264,80,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7792 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 194 268 88 52 33 66 133 261), lower := (rows 35 194 268 88 52 33 66 128 256), losses := [] }

theorem u7792 : Upper (D 6) (R 6) [34,192,264,80,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7793 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 268 88 52 33 68 131 259), lower := (rows 35 194 268 88 52 33 68 128 256), losses := [] }

theorem u7793 : Upper (D 6) (R 6) [34,192,264,80,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7794 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 6 },{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(3,1),(3,2)], upper := (rows 35 194 268 104 21 36 65 146 274), lower := (rows 35 194 268 104 21 36 65 128 256), losses := [] }

theorem u7794 : Upper (D 6) (R 6) [34,192,264,96,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7795 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 194 268 104 21 36 66 145 273), lower := (rows 35 194 268 104 21 36 66 128 256), losses := [] }

theorem u7795 : Upper (D 6) (R 6) [34,192,264,96,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7796 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 194 268 104 21 36 80 131 259), lower := (rows 35 194 268 104 21 36 80 128 256), losses := [] }

theorem u7796 : Upper (D 6) (R 6) [34,192,264,96,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7796 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7797 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 268 104 21 48 65 134 262), lower := (rows 35 194 268 104 21 48 65 128 256), losses := [] }

theorem u7797 : Upper (D 6) (R 6) [34,192,264,96,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7797 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7798 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 194 268 104 21 48 66 133 261), lower := (rows 35 194 268 104 21 48 66 128 256), losses := [] }

theorem u7798 : Upper (D 6) (R 6) [34,192,264,96,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7798 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7799 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 194 268 104 21 48 68 131 259), lower := (rows 35 194 268 104 21 48 68 128 256), losses := [] }

theorem u7799 : Upper (D 6) (R 6) [34,192,264,96,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7799 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7799
end Delivery.IrregularNine14.P06
