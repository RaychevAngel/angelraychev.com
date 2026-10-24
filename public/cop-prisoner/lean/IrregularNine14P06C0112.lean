import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6720 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 4 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 35 131 261 28 82 36 96 200 328), lower := (rows 35 131 261 28 82 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 19 44 109 172 300), good := (rows 498 210 508 508 82 492 480 128 256) }] }

theorem u6720 : Upper (D 6) (R 6) [34,129,257,20,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6721 : Route 9 := (fun mask => (mask,id))

def c6721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6721 : Upper (D 6) (R 6) [34,129,257,20,66,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,20,66,64,4] 13 (by decide) (choices 1) [8,32] r6721 c6721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u505
  · exact u506

def b6722 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 261 28 82 96 72 164 292), lower := (rows 35 131 261 28 82 96 72 128 256), losses := [] }

theorem u6722 : Upper (D 6) (R 6) [34,129,257,20,66,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6722 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6723 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 115, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 131 261 28 82 96 96 140 268), lower := (rows 35 131 261 28 82 96 96 128 256), losses := [] }

theorem u6723 : Upper (D 6) (R 6) [34,129,257,20,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6724 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 4 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 35 131 261 28 112 36 66 200 328), lower := (rows 35 131 261 28 112 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 44 21 44 67 149 277), good := (rows 506 466 508 444 504 444 66 128 256) }] }

theorem u6724 : Upper (D 6) (R 6) [34,129,257,20,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6725 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 261 28 112 36 72 194 322), lower := (rows 35 131 261 28 112 36 72 128 256), losses := [] }

theorem u6725 : Upper (D 6) (R 6) [34,129,257,20,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6725 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6726 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 131 261 44 82 96 68 152 280), lower := (rows 35 131 261 44 82 96 68 128 256), losses := [] }

theorem u6726 : Upper (D 6) (R 6) [34,129,257,36,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6727 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 261 44 82 96 72 148 276), lower := (rows 35 131 261 44 82 96 72 128 256), losses := [] }

theorem u6727 : Upper (D 6) (R 6) [34,129,257,36,66,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6727 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6728 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 261 44 82 96 80 140 268), lower := (rows 35 131 261 44 82 96 80 128 256), losses := [] }

theorem u6728 : Upper (D 6) (R 6) [34,129,257,36,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6728 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6729 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 40, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 131 261 44 84 96 66 152 280), lower := (rows 35 131 261 44 84 96 66 128 256), losses := [] }

theorem u6729 : Upper (D 6) (R 6) [34,129,257,36,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6730 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 261 44 84 96 72 146 274), lower := (rows 35 131 261 44 84 96 72 128 256), losses := [] }

theorem u6730 : Upper (D 6) (R 6) [34,129,257,36,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6730 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6731 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 261 44 84 96 80 138 266), lower := (rows 35 131 261 44 84 96 80 128 256), losses := [] }

theorem u6731 : Upper (D 6) (R 6) [34,129,257,36,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6731 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6732 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 35 131 261 44 88 96 66 148 276), lower := (rows 35 131 261 44 88 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 119 67 140 268), good := (rows 98 226 508 444 504 96 98 128 256) }] }

theorem u6732 : Upper (D 6) (R 6) [34,129,257,36,72,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6733 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 261 44 88 96 68 146 274), lower := (rows 35 131 261 44 88 96 68 128 256), losses := [] }

theorem u6733 : Upper (D 6) (R 6) [34,129,257,36,72,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6734 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 261 44 88 96 80 134 262), lower := (rows 35 131 261 44 88 96 80 128 256), losses := [] }

theorem u6734 : Upper (D 6) (R 6) [34,129,257,36,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6734 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6735 : PairBound 9 := { available := 72, camps := [], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 261 56 82 36 68 200 328), lower := (rows 35 131 261 56 82 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 29 17 100 100 253 381), good := (rows 506 410 508 504 506 492 492 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 100 152 280), good := (rows 97 129 357 504 504 100 100 128 256) }] }

theorem u6735 : Upper (D 6) (R 6) [34,129,257,48,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6736 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 88, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 131 261 56 82 36 72 196 324), lower := (rows 35 131 261 56 82 36 72 128 256), losses := [] }

theorem u6736 : Upper (D 6) (R 6) [34,129,257,48,66,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6736 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6737 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 72, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 35 131 261 74 84 36 72 176 304), lower := (rows 35 131 261 74 84 36 72 128 256), losses := [] }

theorem u6737 : Upper (D 6) (R 6) [34,129,257,66,68,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6737 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6738 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 261 74 84 36 80 168 296), lower := (rows 35 131 261 74 84 36 80 128 256), losses := [] }

theorem u6738 : Upper (D 6) (R 6) [34,129,257,66,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6738 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6739 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 0, region := 72, targets := 1 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 35 131 261 74 84 36 96 152 280), lower := (rows 35 131 261 74 84 36 96 128 256), losses := [] }

theorem u6739 : Upper (D 6) (R 6) [34,129,257,66,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6740 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 261 74 84 48 68 168 296), lower := (rows 35 131 261 74 84 48 68 128 256), losses := [] }

theorem u6740 : Upper (D 6) (R 6) [34,129,257,66,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6740 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6741 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 35 131 261 74 84 48 72 164 292), lower := (rows 35 131 261 74 84 48 72 128 256), losses := [] }

theorem u6741 : Upper (D 6) (R 6) [34,129,257,66,68,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6741 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6742 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 261 74 84 48 96 140 268), lower := (rows 35 131 261 74 84 48 96 128 256), losses := [] }

theorem u6742 : Upper (D 6) (R 6) [34,129,257,66,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6742 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6743 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 261 74 112 36 68 152 280), lower := (rows 35 131 261 74 112 36 68 128 256), losses := [] }

theorem u6743 : Upper (D 6) (R 6) [34,129,257,66,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6744 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 72, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 35 131 261 74 112 36 72 148 276), lower := (rows 35 131 261 74 112 36 72 128 256), losses := [] }

theorem u6744 : Upper (D 6) (R 6) [34,129,257,66,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6744 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6745 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 261 74 112 36 80 140 268), lower := (rows 35 131 261 74 112 36 80 128 256), losses := [] }

theorem u6745 : Upper (D 6) (R 6) [34,129,257,66,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6745 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6746 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 0, region := 80, targets := 4 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 261 76 112 36 66 152 280), lower := (rows 35 131 261 76 112 36 66 128 256), losses := [] }

theorem u6746 : Upper (D 6) (R 6) [34,129,257,68,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6747 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 261 76 112 36 72 146 274), lower := (rows 35 131 261 76 112 36 72 128 256), losses := [] }

theorem u6747 : Upper (D 6) (R 6) [34,129,257,68,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6747 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6748 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 261 76 112 36 80 138 266), lower := (rows 35 131 261 76 112 36 80 128 256), losses := [] }

theorem u6748 : Upper (D 6) (R 6) [34,129,257,68,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6748 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6749 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 262 13 52 96 72 208 336), lower := (rows 35 131 262 13 52 96 72 128 256), losses := [] }

theorem u6749 : Upper (D 6) (R 6) [34,129,258,5,36,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6749 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6750 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 262 13 52 96 80 200 328), lower := (rows 35 131 262 13 52 96 80 128 256), losses := [] }

theorem u6750 : Upper (D 6) (R 6) [34,129,258,5,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6750 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6751 : Route 9 := (fun mask => (mask,id))

def c6751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6751 : Upper (D 6) (R 6) [34,129,258,5,40,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,258,5,40,64,4] 13 (by decide) (choices 1) [16,64] r6751 c6751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u507
  · exact u508

def b6752 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 262 13 56 96 80 196 324), lower := (rows 35 131 262 13 56 96 80 128 256), losses := [] }

theorem u6752 : Upper (D 6) (R 6) [34,129,258,5,40,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6752 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6753 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 262 13 84 96 72 176 304), lower := (rows 35 131 262 13 84 96 72 128 256), losses := [] }

theorem u6753 : Upper (D 6) (R 6) [34,129,258,5,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6753 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6754 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 262 13 84 96 80 168 296), lower := (rows 35 131 262 13 84 96 80 128 256), losses := [] }

theorem u6754 : Upper (D 6) (R 6) [34,129,258,5,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6754 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6755 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 262 13 84 96 96 152 280), lower := (rows 35 131 262 13 84 96 96 128 256), losses := [] }

theorem u6755 : Upper (D 6) (R 6) [34,129,258,5,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6756 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 3 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 262 13 88 96 68 176 304), lower := (rows 35 131 262 13 88 96 68 128 256), losses := [] }

theorem u6756 : Upper (D 6) (R 6) [34,129,258,5,72,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6757 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 262 13 88 96 80 164 292), lower := (rows 35 131 262 13 88 96 80 128 256), losses := [] }

theorem u6757 : Upper (D 6) (R 6) [34,129,258,5,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6757 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6758 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 262 13 88 96 96 148 276), lower := (rows 35 131 262 13 88 96 96 128 256), losses := [] }

theorem u6758 : Upper (D 6) (R 6) [34,129,258,5,72,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6759 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 131, targets := 4 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 262 25 28 96 68 224 352), lower := (rows 35 131 262 25 28 96 68 128 256), losses := [] }

theorem u6759 : Upper (D 6) (R 6) [34,129,258,17,12,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6760 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 262 25 28 96 96 196 324), lower := (rows 35 131 262 25 28 96 96 128 256), losses := [] }

theorem u6760 : Upper (D 6) (R 6) [34,129,258,17,12,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6761 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 131 262 25 52 96 68 200 328), lower := (rows 35 131 262 25 52 96 68 128 256), losses := [] }

theorem u6761 : Upper (D 6) (R 6) [34,129,258,17,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6762 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 262 25 52 96 72 196 324), lower := (rows 35 131 262 25 52 96 72 128 256), losses := [] }

theorem u6762 : Upper (D 6) (R 6) [34,129,258,17,36,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6762 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6763 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 131 262 25 84 36 72 224 352), lower := (rows 35 131 262 25 84 36 72 128 256), losses := [{ target := 6, region := (rows 5 2 4 24 16 52 0 128 256), good := (rows 35 131 295 57 61 37 8 128 256) }] }

theorem u6763 : Upper (D 6) (R 6) [34,129,258,17,68,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6763 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6764 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 262 25 84 36 96 200 328), lower := (rows 35 131 262 25 84 36 96 128 256), losses := [] }

theorem u6764 : Upper (D 6) (R 6) [34,129,258,17,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6765 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 262 25 84 96 68 168 296), lower := (rows 35 131 262 25 84 96 68 128 256), losses := [] }

theorem u6765 : Upper (D 6) (R 6) [34,129,258,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6766 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 262 25 84 96 72 164 292), lower := (rows 35 131 262 25 84 96 72 128 256), losses := [] }

theorem u6766 : Upper (D 6) (R 6) [34,129,258,17,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6766 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6767 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 131 262 25 84 96 96 140 268), lower := (rows 35 131 262 25 84 96 96 128 256), losses := [] }

theorem u6767 : Upper (D 6) (R 6) [34,129,258,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6768 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 131 262 28 56 96 65 196 324), lower := (rows 35 131 262 28 56 96 65 128 256), losses := [] }

theorem u6768 : Upper (D 6) (R 6) [34,129,258,20,40,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6769 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 262 28 56 96 68 193 321), lower := (rows 35 131 262 28 56 96 68 128 256), losses := [] }

theorem u6769 : Upper (D 6) (R 6) [34,129,258,20,40,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6770 : Route 9 := (fun mask => (mask,id))

def c6770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6770 : Upper (D 6) (R 6) [34,129,258,20,65,4,8] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,65,4,8] 13 (by decide) (choices 1) [32,64] r6770 c6770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u509
  · exact u510

def b6771 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 131 262 28 81 36 96 200 328), lower := (rows 35 131 262 28 81 36 96 128 256), losses := [] }

theorem u6771 : Upper (D 6) (R 6) [34,129,258,20,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6772 : Route 9 := (fun mask => (mask,id))

def c6772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6772 : Upper (D 6) (R 6) [34,129,258,20,65,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,65,64,4] 13 (by decide) (choices 1) [8,32] r6772 c6772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u511
  · exact u512

def b6773 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 262 28 81 96 72 164 292), lower := (rows 35 131 262 28 81 96 72 128 256), losses := [] }

theorem u6773 : Upper (D 6) (R 6) [34,129,258,20,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6773 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6774 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 131 262 28 81 96 96 140 268), lower := (rows 35 131 262 28 81 96 96 128 256), losses := [] }

theorem u6774 : Upper (D 6) (R 6) [34,129,258,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6775 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 131 262 28 112 36 65 200 328), lower := (rows 35 131 262 28 112 36 65 128 256), losses := [] }

theorem u6775 : Upper (D 6) (R 6) [34,129,258,20,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6776 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 262 28 112 36 72 193 321), lower := (rows 35 131 262 28 112 36 72 128 256), losses := [] }

theorem u6776 : Upper (D 6) (R 6) [34,129,258,20,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6776 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6777 : Route 9 := (fun mask => (mask,id))

def c6777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6777 : Upper (D 6) (R 6) [34,129,258,36,65,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,258,36,65,64,4] 13 (by decide) (choices 1) [8,16] r6777 c6777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u513
  · exact u514

def b6778 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 35 131 262 44 81 96 72 148 276), lower := (rows 35 131 262 44 81 96 72 128 256), losses := [] }

theorem u6778 : Upper (D 6) (R 6) [34,129,258,36,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6778 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6779 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 262 44 81 96 80 140 268), lower := (rows 35 131 262 44 81 96 80 128 256), losses := [] }

theorem u6779 : Upper (D 6) (R 6) [34,129,258,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6779 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6779
end Delivery.IrregularNine14.P06
