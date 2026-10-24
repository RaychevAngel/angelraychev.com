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

def b2820 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 134 73 304 96 80 133 261), lower := (rows 11 38 134 73 304 96 80 128 256), losses := [] }

theorem u2820 : Upper (D 6) (R 6) [10,36,130,65,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2820 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2821 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 38 134 73 336 48 65 164 292), lower := (rows 11 38 134 73 336 48 65 128 256), losses := [] }

theorem u2821 : Upper (D 6) (R 6) [10,36,130,65,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2821 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2822 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 134 73 336 48 68 161 289), lower := (rows 11 38 134 73 336 48 68 128 256), losses := [] }

theorem u2822 : Upper (D 6) (R 6) [10,36,130,65,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2822 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2823 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 134 73 336 48 96 133 261), lower := (rows 11 38 134 73 336 48 96 128 256), losses := [] }

theorem u2823 : Upper (D 6) (R 6) [10,36,130,65,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2823 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2824 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 88 21 96 65 416 288), lower := (rows 11 38 134 88 21 96 65 128 256), losses := [] }

theorem u2824 : Upper (D 6) (R 6) [10,36,130,80,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2825 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 134 88 21 96 96 385 257), lower := (rows 11 38 134 88 21 96 96 128 256), losses := [] }

theorem u2825 : Upper (D 6) (R 6) [10,36,130,80,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2826 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 360, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 38 134 88 21 96 320 161 289), lower := (rows 11 38 134 88 21 96 320 128 256), losses := [] }

theorem u2826 : Upper (D 6) (R 6) [10,36,130,80,5,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2826 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2827 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 88 273 96 65 164 292), lower := (rows 11 38 134 88 273 96 65 128 256), losses := [] }

theorem u2827 : Upper (D 6) (R 6) [10,36,130,80,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2828 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 134 88 273 96 68 161 289), lower := (rows 11 38 134 88 273 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 111 70 145 273), good := (rows 505 100 228 504 441 96 100 128 256) }] }

theorem u2828 : Upper (D 6) (R 6) [10,36,130,80,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2829 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 134 88 273 96 96 133 261), lower := (rows 11 38 134 88 273 96 96 128 256), losses := [] }

theorem u2829 : Upper (D 6) (R 6) [10,36,130,80,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2830 : Route 9 := (fun mask => (mask,id))

def c2830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2830 : Upper (D 6) (R 6) [10,36,130,80,260,1,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,260,1,1] 13 (by decide) (choices 1) [32,64] r2830 c2830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u196
  · exact u197

def r2831 : Route 9 := (fun mask => (mask,id))

def c2831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2831 : Upper (D 6) (R 6) [10,36,130,80,260,1,32] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,260,1,32] 13 (by decide) (choices 1) [1,64] r2831 c2831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u198
  · exact u199

def r2832 : Route 9 := (fun mask => (mask,id))

def c2832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2832 : Upper (D 6) (R 6) [10,36,130,80,260,64,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,260,64,1] 13 (by decide) (choices 1) [1,32] r2832 c2832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u200
  · exact u201

def b2833 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 134 88 276 96 96 129 257), lower := (rows 11 38 134 88 276 96 96 128 256), losses := [] }

theorem u2833 : Upper (D 6) (R 6) [10,36,130,80,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2834 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 38 134 88 304 33 65 196 324), lower := (rows 11 38 134 88 304 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 123 19 97 97 130 258), good := (rows 505 508 412 120 376 121 121 128 256) }] }

theorem u2834 : Upper (D 6) (R 6) [10,36,130,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2835 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 38 134 88 304 33 68 193 321), lower := (rows 11 38 134 88 304 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 11 49 33 70 129 257), good := (rows 505 124 204 88 304 441 68 128 256) }] }

theorem u2835 : Upper (D 6) (R 6) [10,36,130,80,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2836 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 132, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(0,6),(2,5),(2,6)], upper := (rows 11 38 134 88 304 96 65 133 261), lower := (rows 11 38 134 88 304 96 65 128 256), losses := [{ target := 6, region := (rows 9 50 45 8 48 32 0 201 329), good := (rows 399 54 134 415 310 438 389 128 256) }] }

theorem u2836 : Upper (D 6) (R 6) [10,36,130,80,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2837 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 132, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 38 134 88 304 96 68 129 257), lower := (rows 11 38 134 88 304 96 68 128 256), losses := [] }

theorem u2837 : Upper (D 6) (R 6) [10,36,130,80,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2838 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 104 84 33 65 400 272), lower := (rows 11 38 134 104 84 33 65 128 256), losses := [] }

theorem u2838 : Upper (D 6) (R 6) [10,36,130,96,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2839 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 134 104 84 33 80 385 257), lower := (rows 11 38 134 104 84 33 80 128 256), losses := [] }

theorem u2839 : Upper (D 6) (R 6) [10,36,130,96,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2839 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2840 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 104 84 33 320 145 273), lower := (rows 11 38 134 104 84 33 320 128 256), losses := [] }

theorem u2840 : Upper (D 6) (R 6) [10,36,130,96,68,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2840 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2841 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 134 104 273 33 68 208 336), lower := (rows 11 38 134 104 273 33 68 128 256), losses := [] }

theorem u2841 : Upper (D 6) (R 6) [10,36,130,96,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2842 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 104 273 33 80 196 324), lower := (rows 11 38 134 104 273 33 80 128 256), losses := [] }

theorem u2842 : Upper (D 6) (R 6) [10,36,130,96,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2842 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2843 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 104 276 33 65 208 336), lower := (rows 11 38 134 104 276 33 65 128 256), losses := [] }

theorem u2843 : Upper (D 6) (R 6) [10,36,130,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2844 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 104 276 33 80 193 321), lower := (rows 11 38 134 104 276 33 80 128 256), losses := [] }

theorem u2844 : Upper (D 6) (R 6) [10,36,130,96,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2844 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2845 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 104 336 33 65 148 276), lower := (rows 11 38 134 104 336 33 65 128 256), losses := [] }

theorem u2845 : Upper (D 6) (R 6) [10,36,130,96,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2846 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 134 104 336 33 68 145 273), lower := (rows 11 38 134 104 336 33 68 128 256), losses := [] }

theorem u2846 : Upper (D 6) (R 6) [10,36,130,96,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2847 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 134 104 336 33 80 133 261), lower := (rows 11 38 134 104 336 33 80 128 256), losses := [] }

theorem u2847 : Upper (D 6) (R 6) [10,36,130,96,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2847 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2848 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 134 265 49 96 68 208 336), lower := (rows 11 38 134 265 49 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 25 25 103 70 129 257), good := (rows 505 100 228 441 441 96 100 128 256) }] }

theorem u2848 : Upper (D 6) (R 6) [10,36,130,257,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2849 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 265 49 96 80 196 324), lower := (rows 11 38 134 265 49 96 80 128 256), losses := [] }

theorem u2849 : Upper (D 6) (R 6) [10,36,130,257,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2849 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2850 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 296, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 134 265 81 96 68 176 304), lower := (rows 11 38 134 265 81 96 68 128 256), losses := [] }

theorem u2850 : Upper (D 6) (R 6) [10,36,130,257,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2851 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 134 265 81 96 80 164 292), lower := (rows 11 38 134 265 81 96 80 128 256), losses := [] }

theorem u2851 : Upper (D 6) (R 6) [10,36,130,257,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2851 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2852 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 265 81 96 96 148 276), lower := (rows 11 38 134 265 81 96 96 128 256), losses := [] }

theorem u2852 : Upper (D 6) (R 6) [10,36,130,257,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2853 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 150, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 265 84 96 65 176 304), lower := (rows 11 38 134 265 84 96 65 128 256), losses := [] }

theorem u2853 : Upper (D 6) (R 6) [10,36,130,257,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2854 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 134 265 84 96 80 161 289), lower := (rows 11 38 134 265 84 96 80 128 256), losses := [] }

theorem u2854 : Upper (D 6) (R 6) [10,36,130,257,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2854 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2855 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 118, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 265 84 96 96 145 273), lower := (rows 11 38 134 265 84 96 96 128 256), losses := [] }

theorem u2855 : Upper (D 6) (R 6) [10,36,130,257,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2856 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 38 134 268 49 96 65 208 336), lower := (rows 11 38 134 268 49 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 81 113 81 241 369), good := (rows 505 428 140 268 497 496 497 128 256) }] }

theorem u2856 : Upper (D 6) (R 6) [10,36,130,260,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2857 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 268 49 96 80 193 321), lower := (rows 11 38 134 268 49 96 80 128 256), losses := [] }

theorem u2857 : Upper (D 6) (R 6) [10,36,130,260,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2857 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2858 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 38 134 268 81 96 65 176 304), lower := (rows 11 38 134 268 81 96 65 128 256), losses := [] }

theorem u2858 : Upper (D 6) (R 6) [10,36,130,260,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2859 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 134 268 81 96 80 161 289), lower := (rows 11 38 134 268 81 96 80 128 256), losses := [] }

theorem u2859 : Upper (D 6) (R 6) [10,36,130,260,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2859 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2860 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 268 81 96 96 145 273), lower := (rows 11 38 134 268 81 96 96 128 256), losses := [] }

theorem u2860 : Upper (D 6) (R 6) [10,36,130,260,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2861 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 38 134 280 21 96 65 224 352), lower := (rows 11 38 134 280 21 96 65 128 256), losses := [] }

theorem u2861 : Upper (D 6) (R 6) [10,36,130,272,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2862 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 38 134 280 21 96 96 193 321), lower := (rows 11 38 134 280 21 96 96 128 256), losses := [] }

theorem u2862 : Upper (D 6) (R 6) [10,36,130,272,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2863 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 5, region := 134, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 280 49 96 65 196 324), lower := (rows 11 38 134 280 49 96 65 128 256), losses := [] }

theorem u2863 : Upper (D 6) (R 6) [10,36,130,272,33,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2864 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 38 134 280 49 96 68 193 321), lower := (rows 11 38 134 280 49 96 68 128 256), losses := [] }

theorem u2864 : Upper (D 6) (R 6) [10,36,130,272,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2865 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 280 81 96 65 164 292), lower := (rows 11 38 134 280 81 96 65 128 256), losses := [] }

theorem u2865 : Upper (D 6) (R 6) [10,36,130,272,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2866 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 296, targets := 6 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 38 134 280 81 96 68 161 289), lower := (rows 11 38 134 280 81 96 68 128 256), losses := [] }

theorem u2866 : Upper (D 6) (R 6) [10,36,130,272,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2867 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 132, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 38 134 280 81 96 96 133 261), lower := (rows 11 38 134 280 81 96 96 128 256), losses := [] }

theorem u2867 : Upper (D 6) (R 6) [10,36,130,272,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2868 : PairBound 9 := { available := 96, camps := [], pairs := [(3,1),(3,2),(4,1)], upper := (rows 11 38 134 280 84 33 65 224 352), lower := (rows 11 38 134 280 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 31 18 97 97 243 371), good := (rows 505 508 412 408 508 489 489 128 256) },{ target := 2, region := (rows 1 2 0 24 16 97 97 243 371), good := (rows 491 482 386 408 504 481 481 128 256) }] }

theorem u2868 : Upper (D 6) (R 6) [10,36,130,272,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2869 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 11 38 134 280 84 33 96 193 321), lower := (rows 11 38 134 280 84 33 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 11 22 33 99 161 289), good := (rows 505 508 220 280 84 489 480 128 256) }] }

theorem u2869 : Upper (D 6) (R 6) [10,36,130,272,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2870 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 38 134 280 84 96 65 161 289), lower := (rows 11 38 134 280 84 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 113 65 193 321), good := (rows 489 36 132 312 508 480 481 128 256) },{ target := 2, region := (rows 1 2 0 24 16 113 65 193 321), good := (rows 491 34 130 312 504 480 481 128 256) }] }

theorem u2870 : Upper (D 6) (R 6) [10,36,130,272,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2871 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 118, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 280 84 96 96 129 257), lower := (rows 11 38 134 280 84 96 96 128 256), losses := [] }

theorem u2871 : Upper (D 6) (R 6) [10,36,130,272,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2872 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 38 134 280 112 33 65 196 324), lower := (rows 11 38 134 280 112 33 65 128 256), losses := [] }

theorem u2872 : Upper (D 6) (R 6) [10,36,130,272,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2873 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 38 134 280 112 33 68 193 321), lower := (rows 11 38 134 280 112 33 68 128 256), losses := [] }

theorem u2873 : Upper (D 6) (R 6) [10,36,130,272,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2874 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 296, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 134 296 81 33 68 208 336), lower := (rows 11 38 134 296 81 33 68 128 256), losses := [] }

theorem u2874 : Upper (D 6) (R 6) [10,36,130,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2875 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 296 81 33 80 196 324), lower := (rows 11 38 134 296 81 33 80 128 256), losses := [] }

theorem u2875 : Upper (D 6) (R 6) [10,36,130,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2875 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2876 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 38 134 296 81 96 65 148 276), lower := (rows 11 38 134 296 81 96 65 128 256), losses := [] }

theorem u2876 : Upper (D 6) (R 6) [10,36,130,288,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2877 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 296, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 134 296 81 96 68 145 273), lower := (rows 11 38 134 296 81 96 68 128 256), losses := [] }

theorem u2877 : Upper (D 6) (R 6) [10,36,130,288,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2878 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 134 296 81 96 80 133 261), lower := (rows 11 38 134 296 81 96 80 128 256), losses := [] }

theorem u2878 : Upper (D 6) (R 6) [10,36,130,288,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2878 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2879 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 134 296 84 33 65 208 336), lower := (rows 11 38 134 296 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 123 18 97 97 147 275), good := (rows 505 508 412 360 508 489 489 128 256) }] }

theorem u2879 : Upper (D 6) (R 6) [10,36,130,288,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2879
end Delivery.IrregularNine14.P06
