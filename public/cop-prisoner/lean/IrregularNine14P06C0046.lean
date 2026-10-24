import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0003

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2760 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 11 38 133 268 82 96 96 145 273), lower := (rows 11 38 133 268 82 96 96 128 256), losses := [] }

theorem u2760 : Upper (D 6) (R 6) [10,36,129,260,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2761 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 38 133 280 81 96 66 164 292), lower := (rows 11 38 133 280 81 96 66 128 256), losses := [] }

theorem u2761 : Upper (D 6) (R 6) [10,36,129,272,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2762 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 98, targets := 1 },{ cop := 2, region := 80, targets := 2 },{ cop := 2, region := 80, targets := 32 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 38 133 280 81 96 68 162 290), lower := (rows 11 38 133 280 81 96 68 128 256), losses := [] }

theorem u2762 : Upper (D 6) (R 6) [10,36,129,272,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2763 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 132, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 38 133 280 81 96 96 134 262), lower := (rows 11 38 133 280 81 96 96 128 256), losses := [] }

theorem u2763 : Upper (D 6) (R 6) [10,36,129,272,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2764 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 38 133 280 82 96 65 164 292), lower := (rows 11 38 133 280 82 96 65 128 256), losses := [] }

theorem u2764 : Upper (D 6) (R 6) [10,36,129,272,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2765 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 4, region := 297, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 11 38 133 280 82 96 68 161 289), lower := (rows 11 38 133 280 82 96 68 128 256), losses := [] }

theorem u2765 : Upper (D 6) (R 6) [10,36,129,272,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2766 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 11 38 133 280 82 96 96 133 261), lower := (rows 11 38 133 280 82 96 96 128 256), losses := [] }

theorem u2766 : Upper (D 6) (R 6) [10,36,129,272,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2767 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 1 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,1)], upper := (rows 11 38 133 280 84 96 65 162 290), lower := (rows 11 38 133 280 84 96 65 128 256), losses := [] }

theorem u2767 : Upper (D 6) (R 6) [10,36,129,272,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2768 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 1, region := 80, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 11 38 133 280 84 96 66 161 289), lower := (rows 11 38 133 280 84 96 66 128 256), losses := [] }

theorem u2768 : Upper (D 6) (R 6) [10,36,129,272,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2769 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 132, targets := 96 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(2,6)], upper := (rows 11 38 133 280 84 96 96 131 259), lower := (rows 11 38 133 280 84 96 96 128 256), losses := [] }

theorem u2769 : Upper (D 6) (R 6) [10,36,129,272,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2770 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 132, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 38 133 296 81 96 66 148 276), lower := (rows 11 38 133 296 81 96 66 128 256), losses := [] }

theorem u2770 : Upper (D 6) (R 6) [10,36,129,288,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2771 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 133 296 81 96 68 146 274), lower := (rows 11 38 133 296 81 96 68 128 256), losses := [] }

theorem u2771 : Upper (D 6) (R 6) [10,36,129,288,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2772 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 296 81 96 80 134 262), lower := (rows 11 38 133 296 81 96 80 128 256), losses := [] }

theorem u2772 : Upper (D 6) (R 6) [10,36,129,288,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2772 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2773 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,5),(4,2),(4,5)], upper := (rows 11 38 133 296 82 96 65 148 276), lower := (rows 11 38 133 296 82 96 65 128 256), losses := [] }

theorem u2773 : Upper (D 6) (R 6) [10,36,129,288,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2774 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 133 296 82 96 68 145 273), lower := (rows 11 38 133 296 82 96 68 128 256), losses := [] }

theorem u2774 : Upper (D 6) (R 6) [10,36,129,288,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2775 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 296 82 96 80 133 261), lower := (rows 11 38 133 296 82 96 80 128 256), losses := [] }

theorem u2775 : Upper (D 6) (R 6) [10,36,129,288,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2775 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2776 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,2),(4,5)], upper := (rows 11 38 133 328 82 48 65 164 292), lower := (rows 11 38 133 328 82 48 65 128 256), losses := [] }

theorem u2776 : Upper (D 6) (R 6) [10,36,129,320,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2776 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2777 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 133 328 82 48 68 161 289), lower := (rows 11 38 133 328 82 48 68 128 256), losses := [] }

theorem u2777 : Upper (D 6) (R 6) [10,36,129,320,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2777 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2778 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 11 38 133 328 82 48 96 133 261), lower := (rows 11 38 133 328 82 48 96 128 256), losses := [] }

theorem u2778 : Upper (D 6) (R 6) [10,36,129,320,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2778 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2779 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,0),(1,6),(4,1)], upper := (rows 11 38 133 328 84 34 65 176 304), lower := (rows 11 38 133 328 84 34 65 128 256), losses := [] }

theorem u2779 : Upper (D 6) (R 6) [10,36,129,320,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2780 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 328 84 34 80 161 289), lower := (rows 11 38 133 328 84 34 80 128 256), losses := [] }

theorem u2780 : Upper (D 6) (R 6) [10,36,129,320,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2780 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2781 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 328 84 34 96 145 273), lower := (rows 11 38 133 328 84 34 96 128 256), losses := [] }

theorem u2781 : Upper (D 6) (R 6) [10,36,129,320,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2782 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 133 328 112 34 65 148 276), lower := (rows 11 38 133 328 112 34 65 128 256), losses := [] }

theorem u2782 : Upper (D 6) (R 6) [10,36,129,320,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2783 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 328 112 34 68 145 273), lower := (rows 11 38 133 328 112 34 68 128 256), losses := [] }

theorem u2783 : Upper (D 6) (R 6) [10,36,129,320,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2784 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 328 112 34 80 133 261), lower := (rows 11 38 133 328 112 34 80 128 256), losses := [] }

theorem u2784 : Upper (D 6) (R 6) [10,36,129,320,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2784 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2785 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 134 25 84 96 65 416 288), lower := (rows 11 38 134 25 84 96 65 128 256), losses := [] }

theorem u2785 : Upper (D 6) (R 6) [10,36,130,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2786 : PairBound 9 := { available := 257, camps := [{ cop := 7, region := 118, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 25 84 96 96 385 257), lower := (rows 11 38 134 25 84 96 96 128 256), losses := [] }

theorem u2786 : Upper (D 6) (R 6) [10,36,130,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2787 : Route 9 := (fun mask => (mask,id))

def c2787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2787 : Upper (D 6) (R 6) [10,36,130,17,68,64,256] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,68,64,256] 13 (by decide) (choices 1) [1,32] r2787 c2787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u188
  · exact u189

def b2788 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 134 25 84 288 65 224 352), lower := (rows 11 38 134 25 84 288 65 128 256), losses := [] }

theorem u2788 : Upper (D 6) (R 6) [10,36,130,17,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2788 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2789 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 134 25 84 288 96 193 321), lower := (rows 11 38 134 25 84 288 96 128 256), losses := [] }

theorem u2789 : Upper (D 6) (R 6) [10,36,130,17,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2789 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2790 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 134 25 112 288 65 196 324), lower := (rows 11 38 134 25 112 288 65 128 256), losses := [] }

theorem u2790 : Upper (D 6) (R 6) [10,36,130,17,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2790 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2791 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(2,5),(4,0)], upper := (rows 11 38 134 25 112 288 68 193 321), lower := (rows 11 38 134 25 112 288 68 128 256), losses := [] }

theorem u2791 : Upper (D 6) (R 6) [10,36,130,17,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2791 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2792 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 25 276 96 65 224 352), lower := (rows 11 38 134 25 276 96 65 128 256), losses := [] }

theorem u2792 : Upper (D 6) (R 6) [10,36,130,17,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2793 : Route 9 := (fun mask => (mask,id))

def c2793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2793 : Upper (D 6) (R 6) [10,36,130,17,260,64,32] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,260,64,32] 13 (by decide) (choices 1) [1,64] r2793 c2793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u190
  · exact u191

def b2794 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 25 304 96 65 196 324), lower := (rows 11 38 134 25 304 96 65 128 256), losses := [] }

theorem u2794 : Upper (D 6) (R 6) [10,36,130,17,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2795 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 38 134 25 304 96 68 193 321), lower := (rows 11 38 134 25 304 96 68 128 256), losses := [] }

theorem u2795 : Upper (D 6) (R 6) [10,36,130,17,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2796 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 25 336 96 65 164 292), lower := (rows 11 38 134 25 336 96 65 128 256), losses := [] }

theorem u2796 : Upper (D 6) (R 6) [10,36,130,17,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2797 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 134 25 336 96 68 161 289), lower := (rows 11 38 134 25 336 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 119 70 137 265), good := (rows 505 100 228 441 368 96 100 128 256) }] }

theorem u2797 : Upper (D 6) (R 6) [10,36,130,17,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2798 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 38 134 25 336 96 96 133 261), lower := (rows 11 38 134 25 336 96 96 128 256), losses := [] }

theorem u2798 : Upper (D 6) (R 6) [10,36,130,17,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2799 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 28 273 96 65 224 352), lower := (rows 11 38 134 28 273 96 65 128 256), losses := [] }

theorem u2799 : Upper (D 6) (R 6) [10,36,130,20,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2800 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 28 273 96 96 193 321), lower := (rows 11 38 134 28 273 96 96 128 256), losses := [] }

theorem u2800 : Upper (D 6) (R 6) [10,36,130,20,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2801 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 134 56 273 96 65 196 324), lower := (rows 11 38 134 56 273 96 65 128 256), losses := [] }

theorem u2801 : Upper (D 6) (R 6) [10,36,130,48,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2802 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 134 56 273 96 68 193 321), lower := (rows 11 38 134 56 273 96 68 128 256), losses := [] }

theorem u2802 : Upper (D 6) (R 6) [10,36,130,48,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2803 : Route 9 := (fun mask => (mask,id))

def c2803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2803 : Upper (D 6) (R 6) [10,36,130,48,260,64,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48,260,64,1] 13 (by decide) (choices 1) [1,64] r2803 c2803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u192
  · exact u193

def b2804 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 134 56 336 33 65 196 324), lower := (rows 11 38 134 56 336 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 123 19 97 97 130 258), good := (rows 505 508 412 120 376 121 121 128 256) }] }

theorem u2804 : Upper (D 6) (R 6) [10,36,130,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2805 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 134 56 336 33 68 193 321), lower := (rows 11 38 134 56 336 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 41 17 33 70 129 257), good := (rows 505 108 196 56 336 441 68 128 256) }] }

theorem u2805 : Upper (D 6) (R 6) [10,36,130,48,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2806 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 290, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 38 134 73 84 288 65 176 304), lower := (rows 11 38 134 73 84 288 65 128 256), losses := [] }

theorem u2806 : Upper (D 6) (R 6) [10,36,130,65,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2806 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2807 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5)], upper := (rows 11 38 134 73 84 288 80 161 289), lower := (rows 11 38 134 73 84 288 80 128 256), losses := [] }

theorem u2807 : Upper (D 6) (R 6) [10,36,130,65,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2807 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2808 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 134 73 84 288 96 145 273), lower := (rows 11 38 134 73 84 288 96 128 256), losses := [] }

theorem u2808 : Upper (D 6) (R 6) [10,36,130,65,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2808 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2809 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 134, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 38 134 73 112 288 65 148 276), lower := (rows 11 38 134 73 112 288 65 128 256), losses := [] }

theorem u2809 : Upper (D 6) (R 6) [10,36,130,65,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2809 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2810 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 134 73 112 288 68 145 273), lower := (rows 11 38 134 73 112 288 68 128 256), losses := [] }

theorem u2810 : Upper (D 6) (R 6) [10,36,130,65,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2810 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2811 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 89, targets := 4 }], pairs := [(0,2)], upper := (rows 11 38 134 73 112 288 80 133 261), lower := (rows 11 38 134 73 112 288 80 128 256), losses := [] }

theorem u2811 : Upper (D 6) (R 6) [10,36,130,65,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2811 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2812 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 3, region := 304, targets := 2 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 38 134 73 273 96 68 176 304), lower := (rows 11 38 134 73 273 96 68 128 256), losses := [] }

theorem u2812 : Upper (D 6) (R 6) [10,36,130,65,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2813 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 38 134 73 273 96 80 164 292), lower := (rows 11 38 134 73 273 96 80 128 256), losses := [] }

theorem u2813 : Upper (D 6) (R 6) [10,36,130,65,257,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2813 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2814 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 134 73 273 96 96 148 276), lower := (rows 11 38 134 73 273 96 96 128 256), losses := [] }

theorem u2814 : Upper (D 6) (R 6) [10,36,130,65,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2815 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 73 276 96 65 176 304), lower := (rows 11 38 134 73 276 96 65 128 256), losses := [] }

theorem u2815 : Upper (D 6) (R 6) [10,36,130,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2816 : Route 9 := (fun mask => (mask,id))

def c2816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2816 : Upper (D 6) (R 6) [10,36,130,65,260,64,16] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,260,64,16] 13 (by decide) (choices 1) [1,32] r2816 c2816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u194
  · exact u195

def b2817 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 134 73 276 96 96 145 273), lower := (rows 11 38 134 73 276 96 96 128 256), losses := [] }

theorem u2817 : Upper (D 6) (R 6) [10,36,130,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2818 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 73 304 96 65 148 276), lower := (rows 11 38 134 73 304 96 65 128 256), losses := [] }

theorem u2818 : Upper (D 6) (R 6) [10,36,130,65,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2819 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 3, region := 304, targets := 2 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 38 134 73 304 96 68 145 273), lower := (rows 11 38 134 73 304 96 68 128 256), losses := [] }

theorem u2819 : Upper (D 6) (R 6) [10,36,130,65,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2819
end Delivery.IrregularNine14.P06
