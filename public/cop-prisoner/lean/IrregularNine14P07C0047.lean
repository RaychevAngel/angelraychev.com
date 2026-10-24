import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0002
import IrregularNine14P07C0003

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2820 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 13 104 145 160 66 208 336), lower := (rows 7 290 13 104 145 160 66 128 256), losses := [] }

theorem u2820 : Upper (D 7) (R 7) [6,288,9,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2821 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 13 104 145 160 80 194 322), lower := (rows 7 290 13 104 145 160 80 128 256), losses := [] }

theorem u2821 : Upper (D 7) (R 7) [6,288,9,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2821 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2822 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 13 104 146 48 65 192 448), lower := (rows 7 290 13 104 146 48 65 128 256), losses := [] }

theorem u2822 : Upper (D 7) (R 7) [6,288,9,96,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2822 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2823 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 13 104 146 48 192 193 321), lower := (rows 7 290 13 104 146 48 192 128 256), losses := [] }

theorem u2823 : Upper (D 7) (R 7) [6,288,9,96,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2823 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2824 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 13 104 146 160 65 208 336), lower := (rows 7 290 13 104 146 160 65 128 256), losses := [] }

theorem u2824 : Upper (D 7) (R 7) [6,288,9,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2825 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 13 104 146 160 80 193 321), lower := (rows 7 290 13 104 146 160 80 128 256), losses := [] }

theorem u2825 : Upper (D 7) (R 7) [6,288,9,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2825 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2826 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 13 104 208 160 65 146 274), lower := (rows 7 290 13 104 208 160 65 128 256), losses := [] }

theorem u2826 : Upper (D 7) (R 7) [6,288,9,96,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2827 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 7 290 13 104 208 160 66 145 273), lower := (rows 7 290 13 104 208 160 66 128 256), losses := [] }

theorem u2827 : Upper (D 7) (R 7) [6,288,9,96,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2828 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 290 13 104 208 160 80 131 259), lower := (rows 7 290 13 104 208 160 80 128 256), losses := [] }

theorem u2828 : Upper (D 7) (R 7) [6,288,9,96,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2828 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2829 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(3,0),(4,5),(4,7)], upper := (rows 7 290 13 200 81 160 66 176 304), lower := (rows 7 290 13 200 81 160 66 128 256), losses := [] }

theorem u2829 : Upper (D 7) (R 7) [6,288,9,192,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2830 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 7 290 13 200 81 160 80 162 290), lower := (rows 7 290 13 200 81 160 80 128 256), losses := [] }

theorem u2830 : Upper (D 7) (R 7) [6,288,9,192,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2830 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2831 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 418, targets := 64 },{ cop := 5, region := 72, targets := 2 }], pairs := [(1,0),(1,6),(3,0),(3,1)], upper := (rows 7 290 13 200 81 160 96 146 274), lower := (rows 7 290 13 200 81 160 96 128 256), losses := [] }

theorem u2831 : Upper (D 7) (R 7) [6,288,9,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2832 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 290 13 200 82 33 80 160 416), lower := (rows 7 290 13 200 82 33 80 128 256), losses := [] }

theorem u2832 : Upper (D 7) (R 7) [6,288,9,192,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2832 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2833 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 7 290 13 200 82 33 96 144 400), lower := (rows 7 290 13 200 82 33 96 128 256), losses := [] }

theorem u2833 : Upper (D 7) (R 7) [6,288,9,192,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2834 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 290 13 200 82 33 192 176 304), lower := (rows 7 290 13 200 82 33 192 128 256), losses := [] }

theorem u2834 : Upper (D 7) (R 7) [6,288,9,192,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2835 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 290 13 200 82 48 65 160 416), lower := (rows 7 290 13 200 82 48 65 128 256), losses := [] }

theorem u2835 : Upper (D 7) (R 7) [6,288,9,192,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2835 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2836 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 290 13 200 82 48 96 129 385), lower := (rows 7 290 13 200 82 48 96 128 256), losses := [] }

theorem u2836 : Upper (D 7) (R 7) [6,288,9,192,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2836 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2837 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 13 200 82 48 192 161 289), lower := (rows 7 290 13 200 82 48 192 128 256), losses := [] }

theorem u2837 : Upper (D 7) (R 7) [6,288,9,192,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2837 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2838 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 290 13 200 82 160 65 176 304), lower := (rows 7 290 13 200 82 160 65 128 256), losses := [] }

theorem u2838 : Upper (D 7) (R 7) [6,288,9,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2839 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 290 13 200 82 160 80 161 289), lower := (rows 7 290 13 200 82 160 80 128 256), losses := [] }

theorem u2839 : Upper (D 7) (R 7) [6,288,9,192,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2839 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2840 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 290 13 200 82 160 96 145 273), lower := (rows 7 290 13 200 82 160 96 128 256), losses := [] }

theorem u2840 : Upper (D 7) (R 7) [6,288,9,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2841 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 136, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 290 13 200 112 34 65 144 400), lower := (rows 7 290 13 200 112 34 65 128 256), losses := [] }

theorem u2841 : Upper (D 7) (R 7) [6,288,9,192,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2842 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 290 13 200 112 34 80 129 385), lower := (rows 7 290 13 200 112 34 80 128 256), losses := [] }

theorem u2842 : Upper (D 7) (R 7) [6,288,9,192,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2842 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2843 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 290 13 200 112 34 192 145 273), lower := (rows 7 290 13 200 112 34 192 128 256), losses := [] }

theorem u2843 : Upper (D 7) (R 7) [6,288,9,192,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2844 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 48, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 7 290 13 200 112 160 65 146 274), lower := (rows 7 290 13 200 112 160 65 128 256), losses := [] }

theorem u2844 : Upper (D 7) (R 7) [6,288,9,192,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2845 : Route 9 := (fun mask => (mask,id))

def c2845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2845 : Upper (D 7) (R 7) [6,288,9,192,96,128,2] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,96,128,2] 13 (by decide) (choices 1) [1,16] r2845 c2845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u179
  · exact u180

def b2846 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 290 13 200 112 160 80 131 259), lower := (rows 7 290 13 200 112 160 80 128 256), losses := [] }

theorem u2846 : Upper (D 7) (R 7) [6,288,9,192,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2846 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2847 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 28 41 81 160 66 192 448), lower := (rows 7 290 28 41 81 160 66 128 256), losses := [] }

theorem u2847 : Upper (D 7) (R 7) [6,288,24,33,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2848 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 482, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(2,1),(3,1),(4,5)], upper := (rows 7 290 28 41 81 160 192 194 322), lower := (rows 7 290 28 41 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 28 24 24 224 224 128 256), good := (rows 5 352 28 125 125 224 224 224 256) }] }

theorem u2848 : Upper (D 7) (R 7) [6,288,24,33,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2849 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 28 41 82 160 65 192 448), lower := (rows 7 290 28 41 82 160 65 128 256), losses := [] }

theorem u2849 : Upper (D 7) (R 7) [6,288,24,33,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2850 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,5),(3,1),(4,0),(4,5)], upper := (rows 7 290 28 41 82 160 192 193 321), lower := (rows 7 290 28 41 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 22 370 28 104 114 224 224 224 256) },{ target := 5, region := (rows 1 2 12 8 19 0 237 137 265), good := (rows 471 338 476 477 82 192 192 192 256) }] }

theorem u2850 : Upper (D 7) (R 7) [6,288,24,33,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2851 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 28 73 112 160 65 130 386), lower := (rows 7 290 28 73 112 160 65 128 256), losses := [] }

theorem u2851 : Upper (D 7) (R 7) [6,288,24,65,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2852 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 28 73 112 160 66 129 385), lower := (rows 7 290 28 73 112 160 66 128 256), losses := [] }

theorem u2852 : Upper (D 7) (R 7) [6,288,24,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2853 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 28 73 112 160 192 131 259), lower := (rows 7 290 28 73 112 160 192 128 256), losses := [] }

theorem u2853 : Upper (D 7) (R 7) [6,288,24,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2854 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 290 28 73 146 96 65 160 416), lower := (rows 7 290 28 73 146 96 65 128 256), losses := [] }

theorem u2854 : Upper (D 7) (R 7) [6,288,24,65,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2855 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,7),(2,7),(3,7),(4,5)], upper := (rows 7 290 28 73 146 96 96 129 385), lower := (rows 7 290 28 73 146 96 96 128 256), losses := [] }

theorem u2855 : Upper (D 7) (R 7) [6,288,24,65,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2856 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 0, region := 232, targets := 2 }], pairs := [(0,5),(2,5),(3,1),(3,5)], upper := (rows 7 290 28 73 146 96 192 161 289), lower := (rows 7 290 28 73 146 96 192 128 256), losses := [] }

theorem u2856 : Upper (D 7) (R 7) [6,288,24,65,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2857 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 28 73 146 160 65 224 352), lower := (rows 7 290 28 73 146 160 65 128 256), losses := [] }

theorem u2857 : Upper (D 7) (R 7) [6,288,24,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2858 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 7 290 28 73 146 160 96 193 321), lower := (rows 7 290 28 73 146 160 96 128 256), losses := [{ target := 7, region := (rows 17 2 20 25 16 32 98 0 281), good := (rows 335 354 285 329 351 96 96 0 256) }] }

theorem u2858 : Upper (D 7) (R 7) [6,288,24,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2859 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 290 28 73 176 96 65 130 386), lower := (rows 7 290 28 73 176 96 65 128 256), losses := [] }

theorem u2859 : Upper (D 7) (R 7) [6,288,24,65,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2860 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 180, targets := 2 },{ cop := 8, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(4,1)], upper := (rows 7 290 28 73 176 96 66 129 385), lower := (rows 7 290 28 73 176 96 66 128 256), losses := [] }

theorem u2860 : Upper (D 7) (R 7) [6,288,24,65,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2861 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 48, targets := 3 },{ cop := 0, region := 200, targets := 32 },{ cop := 3, region := 290, targets := 128 }], pairs := [(1,7),(3,5),(4,0),(4,1)], upper := (rows 7 290 28 73 176 96 192 131 259), lower := (rows 7 290 28 73 176 96 192 128 256), losses := [] }

theorem u2861 : Upper (D 7) (R 7) [6,288,24,65,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2862 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 290 28 73 208 160 65 162 290), lower := (rows 7 290 28 73 208 160 65 128 256), losses := [] }

theorem u2862 : Upper (D 7) (R 7) [6,288,24,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2863 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(3,7)], upper := (rows 7 290 28 73 208 160 66 161 289), lower := (rows 7 290 28 73 208 160 66 128 256), losses := [] }

theorem u2863 : Upper (D 7) (R 7) [6,288,24,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2864 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 7 290 28 73 208 160 96 131 259), lower := (rows 7 290 28 73 208 160 96 128 256), losses := [] }

theorem u2864 : Upper (D 7) (R 7) [6,288,24,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2865 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 0, region := 72, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 290 28 74 176 33 65 192 448), lower := (rows 7 290 28 74 176 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 123 97 97 251 379), good := (rows 501 496 412 508 496 497 497 128 256) }] }

theorem u2865 : Upper (D 7) (R 7) [6,288,24,66,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2866 : Route 9 := (fun mask => (mask,id))

def c2866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2866 : Upper (D 7) (R 7) [6,288,24,66,160,1,128] 13 := by
  apply FastRouting.sound _ _ [6,288,24,66,160,1,128] 13 (by decide) (choices 1) [1,64] r2866 c2866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u181
  · exact u182

def b2867 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 0, region := 72, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 290 28 74 176 96 65 129 385), lower := (rows 7 290 28 74 176 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 121 105 65 193 321), good := (rows 501 304 60 508 176 496 497 128 256) }] }

theorem u2867 : Upper (D 7) (R 7) [6,288,24,66,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2868 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 48, targets := 3 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,0),(3,5),(4,0),(4,1)], upper := (rows 7 290 28 74 176 96 192 129 257), lower := (rows 7 290 28 74 176 96 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 208 252 208 128 256), good := (rows 38 290 124 126 240 112 240 240 256) }] }

theorem u2868 : Upper (D 7) (R 7) [6,288,24,66,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2869 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(3,7)], upper := (rows 7 290 28 74 208 160 65 161 289), lower := (rows 7 290 28 74 208 160 65 128 256), losses := [] }

theorem u2869 : Upper (D 7) (R 7) [6,288,24,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2870 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 149, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 290 28 74 208 160 96 129 257), lower := (rows 7 290 28 74 208 160 96 128 256), losses := [] }

theorem u2870 : Upper (D 7) (R 7) [6,288,24,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2871 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 44 25 82 160 65 192 448), lower := (rows 7 290 44 25 82 160 65 128 256), losses := [] }

theorem u2871 : Upper (D 7) (R 7) [6,288,40,17,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2872 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(4,0),(4,5)], upper := (rows 7 290 44 25 82 160 192 193 321), lower := (rows 7 290 44 25 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 22 370 108 24 114 224 224 224 256) }] }

theorem u2872 : Upper (D 7) (R 7) [6,288,40,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2873 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 44 73 82 160 65 144 400), lower := (rows 7 290 44 73 82 160 65 128 256), losses := [] }

theorem u2873 : Upper (D 7) (R 7) [6,288,40,65,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2874 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 44 73 82 160 80 129 385), lower := (rows 7 290 44 73 82 160 80 128 256), losses := [] }

theorem u2874 : Upper (D 7) (R 7) [6,288,40,65,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2874 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2875 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 290 44 73 82 160 192 145 273), lower := (rows 7 290 44 73 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 224 224 128 256), good := (rows 22 370 108 108 114 224 224 224 256) }] }

theorem u2875 : Upper (D 7) (R 7) [6,288,40,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2876 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 7 290 44 73 145 160 66 208 336), lower := (rows 7 290 44 73 145 160 66 128 256), losses := [] }

theorem u2876 : Upper (D 7) (R 7) [6,288,40,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2877 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 290 44 73 145 160 80 194 322), lower := (rows 7 290 44 73 145 160 80 128 256), losses := [] }

theorem u2877 : Upper (D 7) (R 7) [6,288,40,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2877 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2878 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 44 73 146 160 65 208 336), lower := (rows 7 290 44 73 146 160 65 128 256), losses := [] }

theorem u2878 : Upper (D 7) (R 7) [6,288,40,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2879 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 164, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 290 44 73 146 160 80 193 321), lower := (rows 7 290 44 73 146 160 80 128 256), losses := [] }

theorem u2879 : Upper (D 7) (R 7) [6,288,40,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2879 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2879
end Delivery.IrregularNine14.P07
