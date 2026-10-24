import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5760 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 69 152 274 33 68 168 296), lower := (rows 35 194 69 152 274 33 68 128 256), losses := [] }

theorem u5760 : Upper (D 7) (R 7) [34,192,65,144,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5760 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5761 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 194 69 152 274 33 72 164 292), lower := (rows 35 194 69 152 274 33 72 128 256), losses := [] }

theorem u5761 : Upper (D 7) (R 7) [34,192,65,144,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5761 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5762 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 69 152 274 33 96 140 268), lower := (rows 35 194 69 152 274 33 96 128 256), losses := [] }

theorem u5762 : Upper (D 7) (R 7) [34,192,65,144,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5763 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 35 194 69 152 276 33 66 168 296), lower := (rows 35 194 69 152 276 33 66 128 256), losses := [] }

theorem u5763 : Upper (D 7) (R 7) [34,192,65,144,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5764 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 194 69 152 276 33 72 162 290), lower := (rows 35 194 69 152 276 33 72 128 256), losses := [] }

theorem u5764 : Upper (D 7) (R 7) [34,192,65,144,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5764 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5765 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 69 152 276 33 96 138 266), lower := (rows 35 194 69 152 276 33 96 128 256), losses := [] }

theorem u5765 : Upper (D 7) (R 7) [34,192,65,144,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5766 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 35 194 69 152 280 33 66 164 292), lower := (rows 35 194 69 152 280 33 66 128 256), losses := [] }

theorem u5766 : Upper (D 7) (R 7) [34,192,65,144,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5767 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 69 152 280 33 68 162 290), lower := (rows 35 194 69 152 280 33 68 128 256), losses := [] }

theorem u5767 : Upper (D 7) (R 7) [34,192,65,144,264,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5767 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5768 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 69 152 280 33 96 134 262), lower := (rows 35 194 69 152 280 33 96 128 256), losses := [] }

theorem u5768 : Upper (D 7) (R 7) [34,192,65,144,264,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5769 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 35 194 69 152 304 33 66 140 268), lower := (rows 35 194 69 152 304 33 66 128 256), losses := [] }

theorem u5769 : Upper (D 7) (R 7) [34,192,65,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5770 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 69 152 304 33 68 138 266), lower := (rows 35 194 69 152 304 33 68 128 256), losses := [] }

theorem u5770 : Upper (D 7) (R 7) [34,192,65,144,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5770 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5771 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 194 69 152 304 33 72 134 262), lower := (rows 35 194 69 152 304 33 72 128 256), losses := [] }

theorem u5771 : Upper (D 7) (R 7) [34,192,65,144,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5771 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5772 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 194 69 168 273 48 66 140 268), lower := (rows 35 194 69 168 273 48 66 128 256), losses := [] }

theorem u5772 : Upper (D 7) (R 7) [34,192,65,160,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5772 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5773 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 35 194 69 168 273 48 68 138 266), lower := (rows 35 194 69 168 273 48 68 128 256), losses := [] }

theorem u5773 : Upper (D 7) (R 7) [34,192,65,160,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5773 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5774 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 69 168 273 48 72 134 262), lower := (rows 35 194 69 168 273 48 72 128 256), losses := [] }

theorem u5774 : Upper (D 7) (R 7) [34,192,65,160,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5774 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5775 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 35 194 69 168 276 48 65 138 266), lower := (rows 35 194 69 168 276 48 65 128 256), losses := [] }

theorem u5775 : Upper (D 7) (R 7) [34,192,65,160,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5775 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5776 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 194 69 168 276 48 66 137 265), lower := (rows 35 194 69 168 276 48 66 128 256), losses := [] }

theorem u5776 : Upper (D 7) (R 7) [34,192,65,160,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5776 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5777 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 69 168 276 48 72 131 259), lower := (rows 35 194 69 168 276 48 72 128 256), losses := [] }

theorem u5777 : Upper (D 7) (R 7) [34,192,65,160,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5777 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5778 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 152 273 33 66 164 292), lower := (rows 35 194 76 152 273 33 66 128 256), losses := [] }

theorem u5778 : Upper (D 7) (R 7) [34,192,72,144,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5779 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 152 273 33 68 162 290), lower := (rows 35 194 76 152 273 33 68 128 256), losses := [] }

theorem u5779 : Upper (D 7) (R 7) [34,192,72,144,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5779 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5780 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 194 76 152 273 33 96 134 262), lower := (rows 35 194 76 152 273 33 96 128 256), losses := [] }

theorem u5780 : Upper (D 7) (R 7) [34,192,72,144,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5781 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(2,0)], upper := (rows 35 194 76 152 274 33 65 164 292), lower := (rows 35 194 76 152 274 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 70 107 81 32 64 129 257), good := (rows 446 222 94 152 286 440 478 128 256) }] }

theorem u5781 : Upper (D 7) (R 7) [34,192,72,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5782 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 152 274 33 68 161 289), lower := (rows 35 194 76 152 274 33 68 128 256), losses := [] }

theorem u5782 : Upper (D 7) (R 7) [34,192,72,144,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5782 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5783 : Route 9 := (fun mask => (mask,id))

def c5783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5783 : Upper (D 7) (R 7) [34,192,72,144,258,1,32] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,258,1,32] 13 (by decide) (choices 1) [1,4] r5783 c5783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u424
  · exact u425

def b5784 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(2,0)], upper := (rows 35 194 76 152 276 33 65 162 290), lower := (rows 35 194 76 152 276 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 70 107 81 32 64 129 257), good := (rows 446 222 94 152 276 440 478 128 256) }] }

theorem u5784 : Upper (D 7) (R 7) [34,192,72,144,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5785 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 152 276 33 66 161 289), lower := (rows 35 194 76 152 276 33 66 128 256), losses := [] }

theorem u5785 : Upper (D 7) (R 7) [34,192,72,144,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5786 : Route 9 := (fun mask => (mask,id))

def c5786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5786 : Upper (D 7) (R 7) [34,192,72,144,260,1,32] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,260,1,32] 13 (by decide) (choices 1) [1,2] r5786 c5786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u426
  · exact u427

def b5787 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 194 76 152 304 33 65 134 262), lower := (rows 35 194 76 152 304 33 65 128 256), losses := [] }

theorem u5787 : Upper (D 7) (R 7) [34,192,72,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5788 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 152 304 33 66 133 261), lower := (rows 35 194 76 152 304 33 66 128 256), losses := [] }

theorem u5788 : Upper (D 7) (R 7) [34,192,72,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5789 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 152 304 33 68 131 259), lower := (rows 35 194 76 152 304 33 68 128 256), losses := [] }

theorem u5789 : Upper (D 7) (R 7) [34,192,72,144,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5789 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5790 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 168 273 33 66 148 276), lower := (rows 35 194 76 168 273 33 66 128 256), losses := [] }

theorem u5790 : Upper (D 7) (R 7) [34,192,72,160,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5791 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 168 273 33 68 146 274), lower := (rows 35 194 76 168 273 33 68 128 256), losses := [] }

theorem u5791 : Upper (D 7) (R 7) [34,192,72,160,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5791 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5792 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 2, region := 130, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 35 194 76 168 273 33 80 134 262), lower := (rows 35 194 76 168 273 33 80 128 256), losses := [] }

theorem u5792 : Upper (D 7) (R 7) [34,192,72,160,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5792 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5793 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 168 273 48 65 134 262), lower := (rows 35 194 76 168 273 48 65 128 256), losses := [{ target := 0, region := (rows 0 70 68 9 16 48 64 198 326), good := (rows 426 454 462 168 312 48 462 128 256) }] }

theorem u5793 : Upper (D 7) (R 7) [34,192,72,160,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5793 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5794 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 168 273 48 66 133 261), lower := (rows 35 194 76 168 273 48 66 128 256), losses := [] }

theorem u5794 : Upper (D 7) (R 7) [34,192,72,160,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5794 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5795 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 76 168 273 48 68 131 259), lower := (rows 35 194 76 168 273 48 68 128 256), losses := [] }

theorem u5795 : Upper (D 7) (R 7) [34,192,72,160,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5795 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5796 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 76 168 274 33 65 148 276), lower := (rows 35 194 76 168 274 33 65 128 256), losses := [] }

theorem u5796 : Upper (D 7) (R 7) [34,192,72,160,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5797 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 168 274 33 68 145 273), lower := (rows 35 194 76 168 274 33 68 128 256), losses := [] }

theorem u5797 : Upper (D 7) (R 7) [34,192,72,160,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5797 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5798 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 194 76 168 274 33 80 133 261), lower := (rows 35 194 76 168 274 33 80 128 256), losses := [] }

theorem u5798 : Upper (D 7) (R 7) [34,192,72,160,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5798 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5799 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 76 168 276 33 65 146 274), lower := (rows 35 194 76 168 276 33 65 128 256), losses := [] }

theorem u5799 : Upper (D 7) (R 7) [34,192,72,160,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5800 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 168 276 33 66 145 273), lower := (rows 35 194 76 168 276 33 66 128 256), losses := [] }

theorem u5800 : Upper (D 7) (R 7) [34,192,72,160,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5801 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 194 76 168 276 33 80 131 259), lower := (rows 35 194 76 168 276 33 80 128 256), losses := [] }

theorem u5801 : Upper (D 7) (R 7) [34,192,72,160,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5801 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5802 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 194, targets := 32 },{ cop := 0, region := 136, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 35 194 76 168 276 48 65 131 259), lower := (rows 35 194 76 168 276 48 65 128 256), losses := [{ target := 5, region := (rows 1 71 4 8 20 0 65 193 321), good := (rows 451 450 478 136 278 16 451 128 256) }] }

theorem u5802 : Upper (D 7) (R 7) [34,192,72,160,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5802 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5803 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 168 276 48 66 129 257), lower := (rows 35 194 76 168 276 48 66 128 256), losses := [] }

theorem u5803 : Upper (D 7) (R 7) [34,192,72,160,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5803 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5804 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 66, targets := 33 }], pairs := [(0,6),(1,0),(1,5),(4,6)], upper := (rows 35 194 76 265 176 33 66 148 276), lower := (rows 35 194 76 265 176 33 66 128 256), losses := [] }

theorem u5804 : Upper (D 7) (R 7) [34,192,72,257,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5805 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 76 265 176 33 68 146 274), lower := (rows 35 194 76 265 176 33 68 128 256), losses := [] }

theorem u5805 : Upper (D 7) (R 7) [34,192,72,257,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5805 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5806 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 76 265 176 33 80 134 262), lower := (rows 35 194 76 265 176 33 80 128 256), losses := [] }

theorem u5806 : Upper (D 7) (R 7) [34,192,72,257,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5806 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5807 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 2, region := 178, targets := 1 }], pairs := [(1,0),(3,6),(4,6)], upper := (rows 35 194 76 265 176 36 65 146 274), lower := (rows 35 194 76 265 176 36 65 128 256), losses := [] }

theorem u5807 : Upper (D 7) (R 7) [34,192,72,257,160,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5807 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5808 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 194 76 265 176 36 66 145 273), lower := (rows 35 194 76 265 176 36 66 128 256), losses := [] }

theorem u5808 : Upper (D 7) (R 7) [34,192,72,257,160,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5808 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5809 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 76 265 176 36 80 131 259), lower := (rows 35 194 76 265 176 36 80 128 256), losses := [] }

theorem u5809 : Upper (D 7) (R 7) [34,192,72,257,160,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5809 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5810 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 35 194 76 266 176 33 65 148 276), lower := (rows 35 194 76 266 176 33 65 128 256), losses := [] }

theorem u5810 : Upper (D 7) (R 7) [34,192,72,258,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5811 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 76 266 176 33 68 145 273), lower := (rows 35 194 76 266 176 33 68 128 256), losses := [] }

theorem u5811 : Upper (D 7) (R 7) [34,192,72,258,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5811 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5812 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 76 266 176 33 80 133 261), lower := (rows 35 194 76 266 176 33 80 128 256), losses := [] }

theorem u5812 : Upper (D 7) (R 7) [34,192,72,258,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5812 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5813 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 0, region := 144, targets := 1 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(4,0),(4,6)], upper := (rows 35 194 76 268 176 33 65 146 274), lower := (rows 35 194 76 268 176 33 65 128 256), losses := [] }

theorem u5813 : Upper (D 7) (R 7) [34,192,72,260,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5814 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 35 194 76 268 176 33 66 145 273), lower := (rows 35 194 76 268 176 33 66 128 256), losses := [] }

theorem u5814 : Upper (D 7) (R 7) [34,192,72,260,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5815 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 76 268 176 33 80 131 259), lower := (rows 35 194 76 268 176 33 80 128 256), losses := [] }

theorem u5815 : Upper (D 7) (R 7) [34,192,72,260,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5815 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5816 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 2, region := 130, targets := 33 }], pairs := [(0,6),(1,0),(1,5),(4,6)], upper := (rows 35 194 76 280 176 33 65 134 262), lower := (rows 35 194 76 280 176 33 65 128 256), losses := [] }

theorem u5816 : Upper (D 7) (R 7) [34,192,72,272,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5817 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 66, targets := 33 }], pairs := [(0,6),(1,0),(1,5),(4,6)], upper := (rows 35 194 76 280 176 33 66 133 261), lower := (rows 35 194 76 280 176 33 66 128 256), losses := [] }

theorem u5817 : Upper (D 7) (R 7) [34,192,72,272,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5818 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 194 76 280 176 33 68 131 259), lower := (rows 35 194 76 280 176 33 68 128 256), losses := [] }

theorem u5818 : Upper (D 7) (R 7) [34,192,72,272,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5818 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5819 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 240, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 259 13 26 84 160 96 192 448), lower := (rows 35 259 13 26 84 160 96 128 256), losses := [] }

theorem u5819 : Upper (D 7) (R 7) [34,257,9,18,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5819
end Delivery.IrregularNine14.P07
