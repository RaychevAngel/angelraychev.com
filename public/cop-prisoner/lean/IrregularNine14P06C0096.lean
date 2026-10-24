import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0007

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5760 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 3, region := 130, targets := 32 }], pairs := [(1,5),(4,0),(4,2)], upper := (rows 25 134 292 13 82 96 96 131 259), lower := (rows 25 134 292 13 82 96 96 128 256), losses := [] }

theorem u5760 : Upper (D 6) (R 6) [24,132,288,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5761 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 134 292 13 112 34 65 194 322), lower := (rows 25 134 292 13 112 34 65 128 256), losses := [] }

theorem u5761 : Upper (D 6) (R 6) [24,132,288,5,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5762 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 269, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 25 134 292 13 112 34 66 193 321), lower := (rows 25 134 292 13 112 34 66 128 256), losses := [] }

theorem u5762 : Upper (D 6) (R 6) [24,132,288,5,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5763 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 134 292 41 84 34 65 194 322), lower := (rows 25 134 292 41 84 34 65 128 256), losses := [] }

theorem u5763 : Upper (D 6) (R 6) [24,132,288,33,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5764 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 32 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 25 134 292 41 84 34 66 193 321), lower := (rows 25 134 292 41 84 34 66 128 256), losses := [{ target := 2, region := (rows 17 2 0 24 16 98 98 152 280), good := (rows 409 226 352 489 505 98 98 128 256) }] }

theorem u5764 : Upper (D 6) (R 6) [24,132,288,33,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5765 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 134 292 42 81 96 65 134 262), lower := (rows 25 134 292 42 81 96 65 128 256), losses := [] }

theorem u5765 : Upper (D 6) (R 6) [24,132,288,34,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5766 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 134 292 42 81 96 66 133 261), lower := (rows 25 134 292 42 81 96 66 128 256), losses := [] }

theorem u5766 : Upper (D 6) (R 6) [24,132,288,34,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5767 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 1, region := 104, targets := 1 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 25 134 292 42 81 96 68 131 259), lower := (rows 25 134 292 42 81 96 68 128 256), losses := [] }

theorem u5767 : Upper (D 6) (R 6) [24,132,288,34,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5768 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 130, targets := 33 }], pairs := [(1,0),(1,5),(4,1)], upper := (rows 25 134 292 42 84 33 65 194 322), lower := (rows 25 134 292 42 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 97 97 128 256), good := (rows 121 148 372 104 116 97 97 128 256) }] }

theorem u5768 : Upper (D 6) (R 6) [24,132,288,34,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5769 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(0,5),(4,0),(4,5)], upper := (rows 25 134 292 42 84 33 66 193 321), lower := (rows 25 134 292 42 84 33 66 128 256), losses := [{ target := 5, region := (rows 9 2 4 8 18 0 74 137 265), good := (rows 473 214 260 475 84 385 82 128 256) }] }

theorem u5769 : Upper (D 6) (R 6) [24,132,288,34,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5770 : Route 9 := (fun mask => (mask,id))

def c5770 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5770 : Upper (D 6) (R 6) [24,132,288,34,68,64,1] 13 := by
  apply FastRouting.sound _ _ [24,132,288,34,68,64,1] 13 (by decide) (choices 1) [1,2] r5770 c5770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u439
  · exact u440

def b5771 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 120, targets := 1 },{ cop := 1, region := 104, targets := 4 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 25 134 292 42 84 96 66 129 257), lower := (rows 25 134 292 42 84 96 66 128 256), losses := [] }

theorem u5771 : Upper (D 6) (R 6) [24,132,288,34,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5772 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 134 292 74 84 33 65 162 290), lower := (rows 25 134 292 74 84 33 65 128 256), losses := [] }

theorem u5772 : Upper (D 6) (R 6) [24,132,288,66,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5773 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 134 292 74 84 33 66 161 289), lower := (rows 25 134 292 74 84 33 66 128 256), losses := [] }

theorem u5773 : Upper (D 6) (R 6) [24,132,288,66,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5774 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 25 134 292 74 84 33 96 131 259), lower := (rows 25 134 292 74 84 33 96 128 256), losses := [] }

theorem u5774 : Upper (D 6) (R 6) [24,132,288,66,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5775 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 134 292 74 84 34 65 161 289), lower := (rows 25 134 292 74 84 34 65 128 256), losses := [] }

theorem u5775 : Upper (D 6) (R 6) [24,132,288,66,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5776 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 25 134 292 74 84 34 96 129 257), lower := (rows 25 134 292 74 84 34 96 128 256), losses := [] }

theorem u5776 : Upper (D 6) (R 6) [24,132,288,66,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5777 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 134 292 76 112 34 65 131 259), lower := (rows 25 134 292 76 112 34 65 128 256), losses := [] }

theorem u5777 : Upper (D 6) (R 6) [24,132,288,68,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5778 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 269, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 25 134 292 76 112 34 66 129 257), lower := (rows 25 134 292 76 112 34 66 128 256), losses := [] }

theorem u5778 : Upper (D 6) (R 6) [24,132,288,68,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5779 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 260, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 162 292 11 21 96 66 196 324), lower := (rows 25 162 292 11 21 96 66 128 256), losses := [] }

theorem u5779 : Upper (D 6) (R 6) [24,160,288,3,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5780 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 162 292 11 84 96 65 134 262), lower := (rows 25 162 292 11 84 96 65 128 256), losses := [] }

theorem u5780 : Upper (D 6) (R 6) [24,160,288,3,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5781 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 25 162 292 11 84 96 66 133 261), lower := (rows 25 162 292 11 84 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 112 64 137 265), good := (rows 445 160 292 397 116 96 96 128 256) }] }

theorem u5781 : Upper (D 6) (R 6) [24,160,288,3,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5782 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 162 292 11 84 96 68 131 259), lower := (rows 25 162 292 11 84 96 68 128 256), losses := [] }

theorem u5782 : Upper (D 6) (R 6) [24,160,288,3,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5783 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 162 292 14 81 96 65 134 262), lower := (rows 25 162 292 14 81 96 65 128 256), losses := [] }

theorem u5783 : Upper (D 6) (R 6) [24,160,288,6,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5784 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 81, targets := 4 },{ cop := 3, region := 81, targets := 32 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 162 292 14 81 96 66 133 261), lower := (rows 25 162 292 14 81 96 66 128 256), losses := [] }

theorem u5784 : Upper (D 6) (R 6) [24,160,288,6,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5785 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 162 292 74 84 33 65 134 262), lower := (rows 25 162 292 74 84 33 65 128 256), losses := [] }

theorem u5785 : Upper (D 6) (R 6) [24,160,288,66,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5786 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 25 162 292 74 84 33 66 133 261), lower := (rows 25 162 292 74 84 33 66 128 256), losses := [] }

theorem u5786 : Upper (D 6) (R 6) [24,160,288,66,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5787 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 6, region := 260, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 162 324 11 21 34 96 196 324), lower := (rows 25 162 324 11 21 34 96 128 256), losses := [] }

theorem u5787 : Upper (D 6) (R 6) [24,160,320,3,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5788 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 194, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 162 324 11 21 36 96 194 322), lower := (rows 25 162 324 11 21 36 96 128 256), losses := [] }

theorem u5788 : Upper (D 6) (R 6) [24,160,320,3,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5789 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 7, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 162 324 11 21 96 96 134 262), lower := (rows 25 162 324 11 21 96 96 128 256), losses := [] }

theorem u5789 : Upper (D 6) (R 6) [24,160,320,3,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5790 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 162 324 14 112 33 65 134 262), lower := (rows 25 162 324 14 112 33 65 128 256), losses := [] }

theorem u5790 : Upper (D 6) (R 6) [24,160,320,6,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5791 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 3, region := 113, targets := 4 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 25 162 324 14 112 33 66 133 261), lower := (rows 25 162 324 14 112 33 66 128 256), losses := [] }

theorem u5791 : Upper (D 6) (R 6) [24,160,320,6,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5792 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 25 162 324 14 112 33 68 131 259), lower := (rows 25 162 324 14 112 33 68 128 256), losses := [] }

theorem u5792 : Upper (D 6) (R 6) [24,160,320,6,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5793 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 162 324 41 82 36 65 134 262), lower := (rows 25 162 324 41 82 36 65 128 256), losses := [] }

theorem u5793 : Upper (D 6) (R 6) [24,160,320,33,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5794 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 162 324 41 82 36 66 133 261), lower := (rows 25 162 324 41 82 36 66 128 256), losses := [] }

theorem u5794 : Upper (D 6) (R 6) [24,160,320,33,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5795 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 130, targets := 68 },{ cop := 8, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 162 324 41 82 36 68 131 259), lower := (rows 25 162 324 41 82 36 68 128 256), losses := [] }

theorem u5795 : Upper (D 6) (R 6) [24,160,320,33,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5796 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 130, targets := 65 },{ cop := 4, region := 260, targets := 1 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 162 324 44 82 33 65 134 262), lower := (rows 25 162 324 44 82 33 65 128 256), losses := [] }

theorem u5796 : Upper (D 6) (R 6) [24,160,320,36,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5797 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 25 162 324 44 82 33 66 133 261), lower := (rows 25 162 324 44 82 33 66 128 256), losses := [] }

theorem u5797 : Upper (D 6) (R 6) [24,160,320,36,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5798 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 25 162 324 44 82 33 68 131 259), lower := (rows 25 162 324 44 82 33 68 128 256), losses := [] }

theorem u5798 : Upper (D 6) (R 6) [24,160,320,36,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5799 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 25 148 288 66 196 324), lower := (rows 35 67 44 25 148 288 66 128 256), losses := [] }

theorem u5799 : Upper (D 6) (R 6) [34,65,40,17,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5799 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5800 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 25 148 288 68 194 322), lower := (rows 35 67 44 25 148 288 68 128 256), losses := [] }

theorem u5800 : Upper (D 6) (R 6) [34,65,40,17,132,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5800 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5801 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 25 208 288 66 132 260), lower := (rows 35 67 44 25 208 288 66 128 256), losses := [] }

theorem u5801 : Upper (D 6) (R 6) [34,65,40,17,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5801 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5802 : Route 9 := (fun mask => (mask,id))

def c5802 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5802 : Upper (D 6) (R 6) [34,65,40,17,192,256,4] 13 := by
  apply FastRouting.sound _ _ [34,65,40,17,192,256,4] 13 (by decide) (choices 1) [2,4] r5802 c5802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u441
  · exact u442

def b5803 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 26 148 288 65 196 324), lower := (rows 35 67 44 26 148 288 65 128 256), losses := [] }

theorem u5803 : Upper (D 6) (R 6) [34,65,40,18,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5803 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5804 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 26 148 288 68 193 321), lower := (rows 35 67 44 26 148 288 68 128 256), losses := [] }

theorem u5804 : Upper (D 6) (R 6) [34,65,40,18,132,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5804 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5805 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 28 145 288 66 196 324), lower := (rows 35 67 44 28 145 288 66 128 256), losses := [] }

theorem u5805 : Upper (D 6) (R 6) [34,65,40,20,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5805 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5806 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 28 145 288 68 194 322), lower := (rows 35 67 44 28 145 288 68 128 256), losses := [] }

theorem u5806 : Upper (D 6) (R 6) [34,65,40,20,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5806 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5807 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 28 146 288 65 196 324), lower := (rows 35 67 44 28 146 288 65 128 256), losses := [] }

theorem u5807 : Upper (D 6) (R 6) [34,65,40,20,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5807 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5808 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 28 146 288 68 193 321), lower := (rows 35 67 44 28 146 288 68 128 256), losses := [] }

theorem u5808 : Upper (D 6) (R 6) [34,65,40,20,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5808 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5809 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 28 208 288 65 134 262), lower := (rows 35 67 44 28 208 288 65 128 256), losses := [] }

theorem u5809 : Upper (D 6) (R 6) [34,65,40,20,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5809 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5810 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 28 208 288 66 133 261), lower := (rows 35 67 44 28 208 288 66 128 256), losses := [] }

theorem u5810 : Upper (D 6) (R 6) [34,65,40,20,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5810 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5811 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 28 208 288 68 131 259), lower := (rows 35 67 44 28 208 288 68 128 256), losses := [] }

theorem u5811 : Upper (D 6) (R 6) [34,65,40,20,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5811 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5812 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 66, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 67 44 88 145 288 66 132 260), lower := (rows 35 67 44 88 145 288 66 128 256), losses := [] }

theorem u5812 : Upper (D 6) (R 6) [34,65,40,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5812 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5813 : Route 9 := (fun mask => (mask,id))

def c5813 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5813 : Upper (D 6) (R 6) [34,65,40,80,129,256,4] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,129,256,4] 13 (by decide) (choices 1) [2,4] r5813 c5813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u443
  · exact u444

def b5814 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 88 146 288 65 132 260), lower := (rows 35 67 44 88 146 288 65 128 256), losses := [] }

theorem u5814 : Upper (D 6) (R 6) [34,65,40,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5814 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5815 : Route 9 := (fun mask => (mask,id))

def c5815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5815 : Upper (D 6) (R 6) [34,65,40,80,130,256,4] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,130,256,4] 13 (by decide) (choices 1) [1,4] r5815 c5815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u445
  · exact u446

def b5816 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 88 148 288 65 134 262), lower := (rows 35 67 44 88 148 288 65 128 256), losses := [] }

theorem u5816 : Upper (D 6) (R 6) [34,65,40,80,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5816 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5817 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 88 148 288 66 133 261), lower := (rows 35 67 44 88 148 288 66 128 256), losses := [] }

theorem u5817 : Upper (D 6) (R 6) [34,65,40,80,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5817 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5818 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 44 88 148 288 68 131 259), lower := (rows 35 67 44 88 148 288 68 128 256), losses := [] }

theorem u5818 : Upper (D 6) (R 6) [34,65,40,80,132,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5818 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5819 : Route 9 := (fun mask => (mask,id))

def c5819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5819 : Upper (D 6) (R 6) [34,65,40,129,6,256,4] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,6,256,4] 13 (by decide) (choices 1) [16,64] r5819 c5819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u447
  · exact u448

#print axioms u5819
end Delivery.IrregularNine14.P06
