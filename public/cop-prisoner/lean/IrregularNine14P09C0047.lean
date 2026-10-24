import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0003

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2820 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 38 196 137 273 288 72 146 274), lower := (rows 97 38 196 137 273 288 72 128 256), losses := [] }

theorem u2820 : Upper (D 9) (R 9) [96,36,192,129,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2820 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2821 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 5, region := 81, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 137 273 288 80 138 266), lower := (rows 97 38 196 137 273 288 80 128 256), losses := [] }

theorem u2821 : Upper (D 9) (R 9) [96,36,192,129,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2821 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2822 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 1, region := 65, targets := 384 }], pairs := [(0,7),(0,8),(2,5),(3,5)], upper := (rows 97 38 196 137 274 48 65 392 264), lower := (rows 97 38 196 137 274 48 65 128 256), losses := [] }

theorem u2822 : Upper (D 9) (R 9) [96,36,192,129,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2822 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2823 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 97 38 196 137 274 48 72 385 257), lower := (rows 97 38 196 137 274 48 72 128 256), losses := [] }

theorem u2823 : Upper (D 9) (R 9) [96,36,192,129,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2823 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2824 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 140, targets := 32 }], pairs := [(1,8),(2,5),(2,8),(3,8)], upper := (rows 97 38 196 137 274 48 320 137 265), lower := (rows 97 38 196 137 274 48 320 128 256), losses := [] }

theorem u2824 : Upper (D 9) (R 9) [96,36,192,129,258,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2824 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2825 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 3, region := 68, targets := 288 }], pairs := [(0,7),(0,8),(2,5),(2,8),(3,8)], upper := (rows 97 38 196 137 274 288 65 152 280), lower := (rows 97 38 196 137 274 288 65 128 256), losses := [{ target := 8, region := (rows 35 2 28 24 16 32 123 144 0), good := (rows 97 103 196 205 223 97 65 128 0) }] }

theorem u2825 : Upper (D 9) (R 9) [96,36,192,129,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2825 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2826 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 38 196 137 274 288 72 145 273), lower := (rows 97 38 196 137 274 288 72 128 256), losses := [] }

theorem u2826 : Upper (D 9) (R 9) [96,36,192,129,258,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2826 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2827 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 140, targets := 32 }], pairs := [(1,8),(2,5),(2,8),(3,8)], upper := (rows 97 38 196 137 274 288 80 137 265), lower := (rows 97 38 196 137 274 288 80 128 256), losses := [] }

theorem u2827 : Upper (D 9) (R 9) [96,36,192,129,258,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2827 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2828 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 3, region := 68, targets := 288 }], pairs := [(1,0),(2,0),(2,5),(2,8)], upper := (rows 97 38 196 137 280 48 65 386 258), lower := (rows 97 38 196 137 280 48 65 128 256), losses := [] }

theorem u2828 : Upper (D 9) (R 9) [96,36,192,129,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2828 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2829 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 196 137 280 48 66 385 257), lower := (rows 97 38 196 137 280 48 66 128 256), losses := [] }

theorem u2829 : Upper (D 9) (R 9) [96,36,192,129,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2829 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2830 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 137 280 48 320 131 259), lower := (rows 97 38 196 137 280 48 320 128 256), losses := [] }

theorem u2830 : Upper (D 9) (R 9) [96,36,192,129,264,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2830 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2831 : Route 9 := (fun mask => (mask,id))

def c2831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2831 : Upper (D 9) (R 9) [96,36,192,129,264,256,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,129,264,256,1] 13 (by decide) (choices 1) [2,16] r2831 c2831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u183
  · exact u184

def b2832 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(2,5),(3,5),(3,6),(4,5)], upper := (rows 97 38 196 137 280 288 66 145 273), lower := (rows 97 38 196 137 280 288 66 128 256), losses := [] }

theorem u2832 : Upper (D 9) (R 9) [96,36,192,129,264,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2832 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2833 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 137 280 288 80 131 259), lower := (rows 97 38 196 137 280 288 80 128 256), losses := [] }

theorem u2833 : Upper (D 9) (R 9) [96,36,192,129,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2833 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2834 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 398, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(3,5)], upper := (rows 97 38 196 138 273 48 65 392 264), lower := (rows 97 38 196 138 273 48 65 128 256), losses := [] }

theorem u2834 : Upper (D 9) (R 9) [96,36,192,130,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2834 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2835 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 97 38 196 138 273 48 72 385 257), lower := (rows 97 38 196 138 273 48 72 128 256), losses := [] }

theorem u2835 : Upper (D 9) (R 9) [96,36,192,130,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2835 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2836 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 138 273 48 320 137 265), lower := (rows 97 38 196 138 273 48 320 128 256), losses := [] }

theorem u2836 : Upper (D 9) (R 9) [96,36,192,130,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2836 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2837 : Route 9 := (fun mask => (mask,id))

def c2837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2837 : Upper (D 9) (R 9) [96,36,192,130,257,256,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,130,257,256,1] 13 (by decide) (choices 1) [8,16] r2837 c2837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u185
  · exact u186

def b2838 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 38 196 138 273 288 72 145 273), lower := (rows 97 38 196 138 273 288 72 128 256), losses := [] }

theorem u2838 : Upper (D 9) (R 9) [96,36,192,130,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2838 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2839 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 138 273 288 80 137 265), lower := (rows 97 38 196 138 273 288 80 128 256), losses := [] }

theorem u2839 : Upper (D 9) (R 9) [96,36,192,130,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2839 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2840 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 369, targets := 128 },{ cop := 0, region := 388, targets := 32 },{ cop := 1, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(2,5),(4,7)], upper := (rows 97 38 196 138 280 48 65 385 257), lower := (rows 97 38 196 138 280 48 65 128 256), losses := [] }

theorem u2840 : Upper (D 9) (R 9) [96,36,192,130,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2840 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2841 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 138 280 48 320 129 257), lower := (rows 97 38 196 138 280 48 320 128 256), losses := [] }

theorem u2841 : Upper (D 9) (R 9) [96,36,192,130,264,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2841 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2842 : Route 9 := (fun mask => (mask,id))

def c2842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2842 : Upper (D 9) (R 9) [96,36,192,130,264,256,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,130,264,256,1] 13 (by decide) (choices 1) [1,16] r2842 c2842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u187
  · exact u188

def b2843 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 2, region := 289, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 138 280 288 80 129 257), lower := (rows 97 38 196 138 280 288 80 128 256), losses := [] }

theorem u2843 : Upper (D 9) (R 9) [96,36,192,130,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2843 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2844 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 196 152 273 33 66 392 264), lower := (rows 97 38 196 152 273 33 66 128 256), losses := [] }

theorem u2844 : Upper (D 9) (R 9) [96,36,192,144,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2844 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2845 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 97 38 196 152 273 33 72 386 258), lower := (rows 97 38 196 152 273 33 72 128 256), losses := [] }

theorem u2845 : Upper (D 9) (R 9) [96,36,192,144,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2845 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2846 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 6, region := 49, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 97 38 196 152 273 33 320 138 266), lower := (rows 97 38 196 152 273 33 320 128 256), losses := [] }

theorem u2846 : Upper (D 9) (R 9) [96,36,192,144,257,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2846 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2847 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 390, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8)], upper := (rows 97 38 196 152 273 40 65 386 258), lower := (rows 97 38 196 152 273 40 65 128 256), losses := [] }

theorem u2847 : Upper (D 9) (R 9) [96,36,192,144,257,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2847 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2848 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 196 152 273 40 66 385 257), lower := (rows 97 38 196 152 273 40 66 128 256), losses := [] }

theorem u2848 : Upper (D 9) (R 9) [96,36,192,144,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2848 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2849 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(4,7)], upper := (rows 97 38 196 152 273 40 320 131 259), lower := (rows 97 38 196 152 273 40 320 128 256), losses := [] }

theorem u2849 : Upper (D 9) (R 9) [96,36,192,144,257,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2849 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2850 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 65, targets := 384 },{ cop := 5, region := 81, targets := 128 }], pairs := [(0,7),(0,8),(2,5),(2,8),(4,7)], upper := (rows 97 38 196 152 273 288 65 138 266), lower := (rows 97 38 196 152 273 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 81 128 256), good := (rows 65 6 196 220 337 256 65 128 256) },{ target := 8, region := (rows 35 2 12 8 16 32 115 128 0), good := (rows 97 103 196 220 81 97 65 128 0) }] }

theorem u2850 : Upper (D 9) (R 9) [96,36,192,144,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2850 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2851 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(2,5),(3,5),(3,6),(4,5)], upper := (rows 97 38 196 152 273 288 66 137 265), lower := (rows 97 38 196 152 273 288 66 128 256), losses := [] }

theorem u2851 : Upper (D 9) (R 9) [96,36,192,144,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2851 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2852 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 38 196 152 273 288 72 131 259), lower := (rows 97 38 196 152 273 288 72 128 256), losses := [] }

theorem u2852 : Upper (D 9) (R 9) [96,36,192,144,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2852 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2853 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 408, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0),(4,5)], upper := (rows 97 38 196 152 274 33 65 392 264), lower := (rows 97 38 196 152 274 33 65 128 256), losses := [] }

theorem u2853 : Upper (D 9) (R 9) [96,36,192,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2853 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2854 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 97 38 196 152 274 33 72 385 257), lower := (rows 97 38 196 152 274 33 72 128 256), losses := [] }

theorem u2854 : Upper (D 9) (R 9) [96,36,192,144,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2854 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2855 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 97 38 196 152 274 33 320 137 265), lower := (rows 97 38 196 152 274 33 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 336 128 256), good := (rows 96 38 196 220 338 32 320 128 320) }] }

theorem u2855 : Upper (D 9) (R 9) [96,36,192,144,258,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2855 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2856 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 97 38 196 152 274 40 65 385 257), lower := (rows 97 38 196 152 274 40 65 128 256), losses := [] }

theorem u2856 : Upper (D 9) (R 9) [96,36,192,144,258,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2856 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2857 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(4,7)], upper := (rows 97 38 196 152 274 40 320 129 257), lower := (rows 97 38 196 152 274 40 320 128 256), losses := [] }

theorem u2857 : Upper (D 9) (R 9) [96,36,192,144,258,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2857 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2858 : Route 9 := (fun mask => (mask,id))

def c2858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2858 : Upper (D 9) (R 9) [96,36,192,144,258,256,1] 13 := by
  apply FastRouting.sound _ _ [96,36,192,144,258,256,1] 13 (by decide) (choices 1) [1,8] r2858 c2858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u189
  · exact u190

def b2859 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 38 196 152 274 288 72 129 257), lower := (rows 97 38 196 152 274 288 72 128 256), losses := [] }

theorem u2859 : Upper (D 9) (R 9) [96,36,192,144,258,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2859 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2860 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 408, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0),(4,5)], upper := (rows 97 38 196 152 280 33 65 386 258), lower := (rows 97 38 196 152 280 33 65 128 256), losses := [] }

theorem u2860 : Upper (D 9) (R 9) [96,36,192,144,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2860 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2861 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 32 },{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(2,5),(3,5),(4,5)], upper := (rows 97 38 196 152 280 33 66 385 257), lower := (rows 97 38 196 152 280 33 66 128 256), losses := [] }

theorem u2861 : Upper (D 9) (R 9) [96,36,192,144,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2861 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2862 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 167, targets := 256 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,8)], upper := (rows 97 38 196 152 280 33 320 131 259), lower := (rows 97 38 196 152 280 33 320 128 256), losses := [] }

theorem u2862 : Upper (D 9) (R 9) [96,36,192,144,264,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2862 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2863 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 196 265 274 33 72 144 400), lower := (rows 97 38 196 265 274 33 72 128 256), losses := [] }

theorem u2863 : Upper (D 9) (R 9) [96,36,192,257,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2863 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2864 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 196 265 274 33 80 136 392), lower := (rows 97 38 196 265 274 33 80 128 256), losses := [] }

theorem u2864 : Upper (D 9) (R 9) [96,36,192,257,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2864 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2865 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,7),(4,7)], upper := (rows 97 38 196 265 274 33 192 152 280), lower := (rows 97 38 196 265 274 33 192 128 256), losses := [] }

theorem u2865 : Upper (D 9) (R 9) [96,36,192,257,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2865 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2866 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 406, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 97 38 196 265 274 40 65 144 400), lower := (rows 97 38 196 265 274 40 65 128 256), losses := [] }

theorem u2866 : Upper (D 9) (R 9) [96,36,192,257,258,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2866 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2867 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 396, targets := 32 },{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8),(2,5),(3,5)], upper := (rows 97 38 196 265 274 40 80 129 385), lower := (rows 97 38 196 265 274 40 80 128 256), losses := [] }

theorem u2867 : Upper (D 9) (R 9) [96,36,192,257,258,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2867 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2868 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 97 38 196 265 274 40 192 145 273), lower := (rows 97 38 196 265 274 40 192 128 256), losses := [] }

theorem u2868 : Upper (D 9) (R 9) [96,36,192,257,258,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2868 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2869 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 196 265 400 33 66 152 280), lower := (rows 97 38 196 265 400 33 66 128 256), losses := [] }

theorem u2869 : Upper (D 9) (R 9) [96,36,192,257,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2869 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2870 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 196 265 400 33 72 146 274), lower := (rows 97 38 196 265 400 33 72 128 256), losses := [] }

theorem u2870 : Upper (D 9) (R 9) [96,36,192,257,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2870 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2871 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,7)], upper := (rows 97 38 196 265 400 33 80 138 266), lower := (rows 97 38 196 265 400 33 80 128 256), losses := [] }

theorem u2871 : Upper (D 9) (R 9) [96,36,192,257,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2871 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2872 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 97 38 196 265 400 40 65 146 274), lower := (rows 97 38 196 265 400 40 65 128 256), losses := [] }

theorem u2872 : Upper (D 9) (R 9) [96,36,192,257,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2872 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2873 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 196 265 400 40 66 145 273), lower := (rows 97 38 196 265 400 40 66 128 256), losses := [] }

theorem u2873 : Upper (D 9) (R 9) [96,36,192,257,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2873 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2874 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 97 38 196 265 400 40 80 131 259), lower := (rows 97 38 196 265 400 40 80 128 256), losses := [] }

theorem u2874 : Upper (D 9) (R 9) [96,36,192,257,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2874 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2875 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 103, targets := 256 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 97 38 196 265 400 48 65 138 266), lower := (rows 97 38 196 265 400 48 65 128 256), losses := [] }

theorem u2875 : Upper (D 9) (R 9) [96,36,192,257,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2875 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2876 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 97 38 196 265 400 48 66 137 265), lower := (rows 97 38 196 265 400 48 66 128 256), losses := [] }

theorem u2876 : Upper (D 9) (R 9) [96,36,192,257,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2876 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2877 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 329, targets := 128 }], pairs := [(0,7),(1,8),(2,8)], upper := (rows 97 38 196 265 400 48 72 131 259), lower := (rows 97 38 196 265 400 48 72 128 256), losses := [] }

theorem u2877 : Upper (D 9) (R 9) [96,36,192,257,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2877 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2878 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 408, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0),(4,5)], upper := (rows 97 38 196 266 400 33 65 152 280), lower := (rows 97 38 196 266 400 33 65 128 256), losses := [] }

theorem u2878 : Upper (D 9) (R 9) [96,36,192,258,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2878 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2879 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 38 196 266 400 33 72 145 273), lower := (rows 97 38 196 266 400 33 72 128 256), losses := [] }

theorem u2879 : Upper (D 9) (R 9) [96,36,192,258,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2879 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2879
end Delivery.IrregularNine14.P09
