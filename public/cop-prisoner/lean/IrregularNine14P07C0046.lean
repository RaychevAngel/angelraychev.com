import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0002

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2760 : Route 9 := (fun mask => (mask,id))

def c2760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2760 : Upper (D 7) (R 7) [6,264,96,17,160,2,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17,160,2,128] 13 (by decide) (choices 1) [1,64] r2760 c2760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u174
  · exact u175

def b2761 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5),(4,5)], upper := (rows 7 266 100 26 145 33 96 192 448), lower := (rows 7 266 100 26 145 33 96 128 256), losses := [] }

theorem u2761 : Upper (D 7) (R 7) [6,264,96,18,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2762 : Route 9 := (fun mask => (mask,id))

def c2762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2762 : Upper (D 7) (R 7) [6,264,96,18,129,1,128] 13 := by
  apply FastRouting.sound _ _ [6,264,96,18,129,1,128] 13 (by decide) (choices 1) [32,64] r2762 c2762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u176
  · exact u177

def b2763 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 266 100 26 145 96 192 161 289), lower := (rows 7 266 100 26 145 96 192 128 256), losses := [] }

theorem u2763 : Upper (D 7) (R 7) [6,264,96,18,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2764 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 68, targets := 130 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,7),(4,5)], upper := (rows 7 266 100 41 82 160 65 144 400), lower := (rows 7 266 100 41 82 160 65 128 256), losses := [] }

theorem u2764 : Upper (D 7) (R 7) [6,264,96,33,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2765 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 266 100 41 82 160 80 129 385), lower := (rows 7 266 100 41 82 160 80 128 256), losses := [] }

theorem u2765 : Upper (D 7) (R 7) [6,264,96,33,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2765 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2766 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 266 100 41 82 160 192 145 273), lower := (rows 7 266 100 41 82 160 192 128 256), losses := [] }

theorem u2766 : Upper (D 7) (R 7) [6,264,96,33,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2767 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 68, targets := 130 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,7),(4,5)], upper := (rows 7 266 100 41 146 160 65 208 336), lower := (rows 7 266 100 41 146 160 65 128 256), losses := [] }

theorem u2767 : Upper (D 7) (R 7) [6,264,96,33,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2768 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 266 100 41 146 160 80 193 321), lower := (rows 7 266 100 41 146 160 80 128 256), losses := [] }

theorem u2768 : Upper (D 7) (R 7) [6,264,96,33,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2768 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2769 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 266 100 42 145 160 65 208 336), lower := (rows 7 266 100 42 145 160 65 128 256), losses := [] }

theorem u2769 : Upper (D 7) (R 7) [6,264,96,34,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2770 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 266 100 42 145 160 80 193 321), lower := (rows 7 266 100 42 145 160 80 128 256), losses := [] }

theorem u2770 : Upper (D 7) (R 7) [6,264,96,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2770 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2771 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 266 100 56 81 160 65 130 386), lower := (rows 7 266 100 56 81 160 65 128 256), losses := [] }

theorem u2771 : Upper (D 7) (R 7) [6,264,96,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2772 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 172, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,1),(3,1),(3,6)], upper := (rows 7 266 100 56 81 160 66 129 385), lower := (rows 7 266 100 56 81 160 66 128 256), losses := [] }

theorem u2772 : Upper (D 7) (R 7) [6,264,96,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2773 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 266 100 56 81 160 192 131 259), lower := (rows 7 266 100 56 81 160 192 128 256), losses := [] }

theorem u2773 : Upper (D 7) (R 7) [6,264,96,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2774 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 266 100 56 82 160 65 129 385), lower := (rows 7 266 100 56 82 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 85 24 16 245 65 193 321), good := (rows 485 264 484 60 508 160 485 160 256) }] }

theorem u2774 : Upper (D 7) (R 7) [6,264,96,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2775 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 266 100 56 82 160 192 129 257), lower := (rows 7 266 100 56 82 160 192 128 256), losses := [] }

theorem u2775 : Upper (D 7) (R 7) [6,264,96,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2776 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 266 100 56 146 33 65 192 448), lower := (rows 7 266 100 56 146 33 65 128 256), losses := [] }

theorem u2776 : Upper (D 7) (R 7) [6,264,96,48,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2777 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,5),(2,0),(2,1),(4,5)], upper := (rows 7 266 100 56 146 33 192 193 321), lower := (rows 7 266 100 56 146 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 208 128 256), good := (rows 6 270 100 124 210 32 192 192 256) },{ target := 5, region := (rows 1 10 4 8 25 0 253 161 289), good := (rows 471 346 452 474 210 465 192 192 256) }] }

theorem u2777 : Upper (D 7) (R 7) [6,264,96,48,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2778 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 100 56 208 33 65 130 386), lower := (rows 7 266 100 56 208 33 65 128 256), losses := [] }

theorem u2778 : Upper (D 7) (R 7) [6,264,96,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2779 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(2,0),(2,7),(4,5)], upper := (rows 7 266 100 56 208 33 66 129 385), lower := (rows 7 266 100 56 208 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 67 128 256), good := (rows 70 330 100 60 208 100 66 128 256) }] }

theorem u2779 : Upper (D 7) (R 7) [6,264,96,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2780 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 100 56 208 33 192 131 259), lower := (rows 7 266 100 56 208 33 192 128 256), losses := [] }

theorem u2780 : Upper (D 7) (R 7) [6,264,96,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2781 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,5)], upper := (rows 7 266 100 56 208 34 65 129 385), lower := (rows 7 266 100 56 208 34 65 128 256), losses := [] }

theorem u2781 : Upper (D 7) (R 7) [6,264,96,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2782 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 100 56 208 34 192 129 257), lower := (rows 7 266 100 56 208 34 192 128 256), losses := [] }

theorem u2782 : Upper (D 7) (R 7) [6,264,96,48,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2783 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(2,0),(2,7)], upper := (rows 7 266 100 137 146 33 80 224 352), lower := (rows 7 266 100 137 146 33 80 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 17 32 121 164 292), good := (rows 470 330 484 216 210 500 80 128 256) }] }

theorem u2783 : Upper (D 7) (R 7) [6,264,96,129,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2783 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2784 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5),(4,5)], upper := (rows 7 266 100 137 146 33 96 208 336), lower := (rows 7 266 100 137 146 33 96 128 256), losses := [] }

theorem u2784 : Upper (D 7) (R 7) [6,264,96,129,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2785 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 100 137 146 48 96 193 321), lower := (rows 7 266 100 137 146 48 96 128 256), losses := [] }

theorem u2785 : Upper (D 7) (R 7) [6,264,96,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2785 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2786 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 144, targets := 3 }], pairs := [(0,7),(2,7),(4,0),(4,1)], upper := (rows 7 266 100 137 176 33 66 208 336), lower := (rows 7 266 100 137 176 33 66 128 256), losses := [] }

theorem u2786 : Upper (D 7) (R 7) [6,264,96,129,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2787 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 100 137 176 33 80 194 322), lower := (rows 7 266 100 137 176 33 80 128 256), losses := [] }

theorem u2787 : Upper (D 7) (R 7) [6,264,96,129,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2787 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2788 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 144, targets := 3 }], pairs := [(0,7),(2,7),(4,0),(4,1)], upper := (rows 7 266 100 137 176 34 65 208 336), lower := (rows 7 266 100 137 176 34 65 128 256), losses := [] }

theorem u2788 : Upper (D 7) (R 7) [6,264,96,129,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2789 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 100 137 176 34 80 193 321), lower := (rows 7 266 100 137 176 34 80 128 256), losses := [] }

theorem u2789 : Upper (D 7) (R 7) [6,264,96,129,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2789 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2790 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 2, region := 394, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 266 100 138 145 33 80 224 352), lower := (rows 7 266 100 138 145 33 80 128 256), losses := [] }

theorem u2790 : Upper (D 7) (R 7) [6,264,96,130,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2790 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2791 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5),(4,5)], upper := (rows 7 266 100 138 145 33 96 208 336), lower := (rows 7 266 100 138 145 33 96 128 256), losses := [] }

theorem u2791 : Upper (D 7) (R 7) [6,264,96,130,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2792 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 100 138 176 33 65 208 336), lower := (rows 7 266 100 138 176 33 65 128 256), losses := [] }

theorem u2792 : Upper (D 7) (R 7) [6,264,96,130,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2793 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 266 100 138 176 33 80 193 321), lower := (rows 7 266 100 138 176 33 80 128 256), losses := [] }

theorem u2793 : Upper (D 7) (R 7) [6,264,96,130,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2793 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2794 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 100 168 208 33 65 146 274), lower := (rows 7 266 100 168 208 33 65 128 256), losses := [] }

theorem u2794 : Upper (D 7) (R 7) [6,264,96,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2795 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(2,0),(2,7),(4,5)], upper := (rows 7 266 100 168 208 33 66 145 273), lower := (rows 7 266 100 168 208 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 67 128 256), good := (rows 70 330 100 172 208 100 66 128 256) }] }

theorem u2795 : Upper (D 7) (R 7) [6,264,96,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2796 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 266 100 168 208 33 80 131 259), lower := (rows 7 266 100 168 208 33 80 128 256), losses := [] }

theorem u2796 : Upper (D 7) (R 7) [6,264,96,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2796 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2797 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,5)], upper := (rows 7 266 100 168 208 34 65 145 273), lower := (rows 7 266 100 168 208 34 65 128 256), losses := [] }

theorem u2797 : Upper (D 7) (R 7) [6,264,96,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2798 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 266 100 168 208 34 80 129 257), lower := (rows 7 266 100 168 208 34 80 128 256), losses := [] }

theorem u2798 : Upper (D 7) (R 7) [6,264,96,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2798 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2799 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 13 56 81 160 66 192 448), lower := (rows 7 290 13 56 81 160 66 128 256), losses := [] }

theorem u2799 : Upper (D 7) (R 7) [6,288,9,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2800 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(2,1),(3,0),(4,5)], upper := (rows 7 290 13 56 81 160 192 194 322), lower := (rows 7 290 13 56 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 224 224 128 256), good := (rows 5 352 13 124 125 224 224 224 256) }] }

theorem u2800 : Upper (D 7) (R 7) [6,288,9,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2801 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 13 56 82 160 65 192 448), lower := (rows 7 290 13 56 82 160 65 128 256), losses := [] }

theorem u2801 : Upper (D 7) (R 7) [6,288,9,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2802 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(3,0),(3,1),(4,0),(4,5)], upper := (rows 7 290 13 56 82 160 192 193 321), lower := (rows 7 290 13 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 26 18 224 224 128 256), good := (rows 30 378 12 120 122 224 224 224 256) },{ target := 1, region := (rows 1 0 4 24 16 229 229 133 261), good := (rows 485 352 493 120 120 224 224 224 256) }] }

theorem u2802 : Upper (D 7) (R 7) [6,288,9,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2803 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 5, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,1)], upper := (rows 7 290 13 88 145 160 66 224 352), lower := (rows 7 290 13 88 145 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 252 64 200 328), good := (rows 53 288 445 504 177 160 480 160 256) }] }

theorem u2803 : Upper (D 7) (R 7) [6,288,9,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2804 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 108, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(3,1)], upper := (rows 7 290 13 88 145 160 96 194 322), lower := (rows 7 290 13 88 145 160 96 128 256), losses := [] }

theorem u2804 : Upper (D 7) (R 7) [6,288,9,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2805 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 4, region := 77, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(3,5)], upper := (rows 7 290 13 88 146 96 65 160 416), lower := (rows 7 290 13 88 146 96 65 128 256), losses := [] }

theorem u2805 : Upper (D 7) (R 7) [6,288,9,80,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2806 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,7),(2,7),(3,7),(4,5)], upper := (rows 7 290 13 88 146 96 96 129 385), lower := (rows 7 290 13 88 146 96 96 128 256), losses := [] }

theorem u2806 : Upper (D 7) (R 7) [6,288,9,80,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2807 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 290 13 88 146 96 192 161 289), lower := (rows 7 290 13 88 146 96 192 128 256), losses := [] }

theorem u2807 : Upper (D 7) (R 7) [6,288,9,80,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2808 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 13 88 146 160 65 224 352), lower := (rows 7 290 13 88 146 160 65 128 256), losses := [] }

theorem u2808 : Upper (D 7) (R 7) [6,288,9,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2809 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(0,7),(2,7),(3,0),(3,1)], upper := (rows 7 290 13 88 146 160 96 193 321), lower := (rows 7 290 13 88 146 160 96 128 256), losses := [{ target := 7, region := (rows 17 2 28 24 16 32 98 0 281), good := (rows 327 354 269 349 351 96 96 0 256) }] }

theorem u2809 : Upper (D 7) (R 7) [6,288,9,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2810 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 7 290 13 88 176 33 66 192 448), lower := (rows 7 290 13 88 176 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 37 64 200 328), good := (rows 53 288 445 472 176 33 448 128 256) }] }

theorem u2810 : Upper (D 7) (R 7) [6,288,9,80,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2811 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 5, region := 450, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 290 13 88 176 33 192 194 322), lower := (rows 7 290 13 88 176 33 192 128 256), losses := [] }

theorem u2811 : Upper (D 7) (R 7) [6,288,9,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2812 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 8, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 7 290 13 88 176 34 65 192 448), lower := (rows 7 290 13 88 176 34 65 128 256), losses := [] }

theorem u2812 : Upper (D 7) (R 7) [6,288,9,80,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2813 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 290 13 88 176 34 192 193 321), lower := (rows 7 290 13 88 176 34 192 128 256), losses := [] }

theorem u2813 : Upper (D 7) (R 7) [6,288,9,80,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2814 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 5, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 7 290 13 88 176 96 65 130 386), lower := (rows 7 290 13 88 176 96 65 128 256), losses := [] }

theorem u2814 : Upper (D 7) (R 7) [6,288,9,80,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2815 : Route 9 := (fun mask => (mask,id))

def c2815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2815 : Upper (D 7) (R 7) [6,288,9,80,160,64,2] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,160,64,2] 13 (by decide) (choices 1) [1] r2815 c2815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u178

def b2816 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 290 13 88 176 96 192 131 259), lower := (rows 7 290 13 88 176 96 192 128 256), losses := [] }

theorem u2816 : Upper (D 7) (R 7) [6,288,9,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2817 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 13 104 82 160 65 144 400), lower := (rows 7 290 13 104 82 160 65 128 256), losses := [] }

theorem u2817 : Upper (D 7) (R 7) [6,288,9,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2818 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 13 104 82 160 80 129 385), lower := (rows 7 290 13 104 82 160 80 128 256), losses := [] }

theorem u2818 : Upper (D 7) (R 7) [6,288,9,96,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2818 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2819 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 290 13 104 82 160 192 145 273), lower := (rows 7 290 13 104 82 160 192 128 256), losses := [] }

theorem u2819 : Upper (D 7) (R 7) [6,288,9,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2819
end Delivery.IrregularNine14.P07
