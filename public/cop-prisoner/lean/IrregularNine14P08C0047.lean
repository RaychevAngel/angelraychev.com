import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0006

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2820 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 168 304 160 81 209 337), lower := (rows 67 14 37 168 304 160 64 128 256), losses := [] }

theorem u2820 : Upper (D 8) (R 8) [66,12,33,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2821 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 168 336 33 240 176 432), lower := (rows 67 14 37 168 336 33 64 128 256), losses := [] }

theorem u2821 : Upper (D 8) (R 8) [66,12,33,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2822 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 14 37 168 336 48 225 161 417), lower := (rows 67 14 37 168 336 48 64 128 256), losses := [] }

theorem u2822 : Upper (D 8) (R 8) [66,12,33,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2822 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2823 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 168 336 160 113 177 305), lower := (rows 67 14 37 168 336 160 64 128 256), losses := [] }

theorem u2823 : Upper (D 8) (R 8) [66,12,33,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2824 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 168 400 33 112 240 368), lower := (rows 67 14 37 168 400 33 64 128 256), losses := [] }

theorem u2824 : Upper (D 8) (R 8) [66,12,33,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2825 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 14 37 168 400 48 97 225 353), lower := (rows 67 14 37 168 400 48 64 128 256), losses := [] }

theorem u2825 : Upper (D 8) (R 8) [66,12,33,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2825 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2826 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 168 400 96 113 177 305), lower := (rows 67 14 37 168 400 96 64 128 256), losses := [] }

theorem u2826 : Upper (D 8) (R 8) [66,12,33,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2827 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 280 176 33 224 224 480), lower := (rows 67 14 37 280 176 33 64 128 256), losses := [] }

theorem u2827 : Upper (D 8) (R 8) [66,12,33,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2828 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 280 176 96 225 161 417), lower := (rows 67 14 37 280 176 96 64 128 256), losses := [] }

theorem u2828 : Upper (D 8) (R 8) [66,12,33,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2829 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 280 176 160 97 225 353), lower := (rows 67 14 37 280 176 160 64 128 256), losses := [] }

theorem u2829 : Upper (D 8) (R 8) [66,12,33,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2830 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 296 112 33 208 144 400), lower := (rows 67 14 37 296 112 33 64 128 256), losses := [] }

theorem u2830 : Upper (D 8) (R 8) [66,12,33,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2831 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 14 37 296 112 48 193 129 385), lower := (rows 67 14 37 296 112 48 64 128 256), losses := [] }

theorem u2831 : Upper (D 8) (R 8) [66,12,33,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2831 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2832 : Route 9 := (fun mask => (mask,id))

def c2832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2832 : Upper (D 8) (R 8) [66,12,33,288,96,128] 13 := by
  apply FastRouting.sound _ _ [66,12,33,288,96,128] 13 (by decide) (choices 1) [1,16,128] r2832 c2832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u363
  · exact u364
  · exact u365

def b2833 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 296 176 33 208 208 464), lower := (rows 67 14 37 296 176 33 64 128 256), losses := [] }

theorem u2833 : Upper (D 8) (R 8) [66,12,33,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2834 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 14 37 296 176 48 193 193 449), lower := (rows 67 14 37 296 176 48 64 128 256), losses := [] }

theorem u2834 : Upper (D 8) (R 8) [66,12,33,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2834 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2835 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 296 176 96 209 145 401), lower := (rows 67 14 37 296 176 96 64 128 256), losses := [] }

theorem u2835 : Upper (D 8) (R 8) [66,12,33,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2836 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 296 176 160 81 209 337), lower := (rows 67 14 37 296 176 160 64 128 256), losses := [] }

theorem u2836 : Upper (D 8) (R 8) [66,12,33,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2837 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 296 208 33 240 176 432), lower := (rows 67 14 37 296 208 33 64 128 256), losses := [] }

theorem u2837 : Upper (D 8) (R 8) [66,12,33,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2838 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 14 37 296 208 48 225 161 417), lower := (rows 67 14 37 296 208 48 64 128 256), losses := [] }

theorem u2838 : Upper (D 8) (R 8) [66,12,33,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2838 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2839 : Route 9 := (fun mask => (mask,id))

def c2839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2839 : Upper (D 8) (R 8) [66,12,33,288,192,128] 13 := by
  apply FastRouting.sound _ _ [66,12,33,288,192,128] 13 (by decide) (choices 1) [1,16,32] r2839 c2839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u366
  · exact u367
  · exact u368

def b2840 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 392 112 33 240 176 432), lower := (rows 67 14 37 392 112 33 64 128 256), losses := [] }

theorem u2840 : Upper (D 8) (R 8) [66,12,33,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2841 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 14 37 392 112 48 225 161 417), lower := (rows 67 14 37 392 112 48 64 128 256), losses := [] }

theorem u2841 : Upper (D 8) (R 8) [66,12,33,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2841 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2842 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 67 14 37 392 112 160 113 177 305), lower := (rows 67 14 37 392 112 160 64 128 256), losses := [] }

theorem u2842 : Upper (D 8) (R 8) [66,12,33,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2843 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 392 176 33 112 240 368), lower := (rows 67 14 37 392 176 33 64 128 256), losses := [] }

theorem u2843 : Upper (D 8) (R 8) [66,12,33,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2844 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 14 37 392 176 48 97 225 353), lower := (rows 67 14 37 392 176 48 64 128 256), losses := [] }

theorem u2844 : Upper (D 8) (R 8) [66,12,33,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2844 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2845 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 392 176 96 113 177 305), lower := (rows 67 14 37 392 176 96 64 128 256), losses := [] }

theorem u2845 : Upper (D 8) (R 8) [66,12,33,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2846 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 37 392 208 33 112 176 304), lower := (rows 67 14 37 392 208 33 64 128 256), losses := [] }

theorem u2846 : Upper (D 8) (R 8) [66,12,33,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2847 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 14 37 392 208 48 97 161 289), lower := (rows 67 14 37 392 208 48 64 128 256), losses := [] }

theorem u2847 : Upper (D 8) (R 8) [66,12,33,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2847 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2848 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 52 168 273 33 224 224 480), lower := (rows 67 14 52 168 273 33 64 128 256), losses := [] }

theorem u2848 : Upper (D 8) (R 8) [66,12,48,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2849 : PairBound 9 := { available := 161, camps := [], pairs := [(2,0)], upper := (rows 67 14 52 168 273 96 225 161 417), lower := (rows 67 14 52 168 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 97 64 128 256), good := (rows 98 14 52 168 308 96 96 128 256) }] }

theorem u2849 : Upper (D 8) (R 8) [66,12,48,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2850 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 52 168 273 160 97 225 353), lower := (rows 67 14 52 168 273 160 64 128 256), losses := [] }

theorem u2850 : Upper (D 8) (R 8) [66,12,48,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2851 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 52 296 145 33 224 224 480), lower := (rows 67 14 52 296 145 33 64 128 256), losses := [] }

theorem u2851 : Upper (D 8) (R 8) [66,12,48,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2852 : PairBound 9 := { available := 161, camps := [], pairs := [(2,0)], upper := (rows 67 14 52 296 145 96 225 161 417), lower := (rows 67 14 52 296 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 97 64 128 256), good := (rows 98 14 52 296 180 96 96 128 256) }] }

theorem u2852 : Upper (D 8) (R 8) [66,12,48,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2853 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 52 296 145 160 97 225 353), lower := (rows 67 14 52 296 145 160 64 128 256), losses := [] }

theorem u2853 : Upper (D 8) (R 8) [66,12,48,288,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2854 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 133 296 112 33 240 176 432), lower := (rows 67 14 133 296 112 33 64 128 256), losses := [] }

theorem u2854 : Upper (D 8) (R 8) [66,12,129,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2855 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 14 133 296 112 48 225 161 417), lower := (rows 67 14 133 296 112 48 64 128 256), losses := [] }

theorem u2855 : Upper (D 8) (R 8) [66,12,129,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2855 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2856 : Route 9 := (fun mask => (mask,id))

def c2856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2856 : Upper (D 8) (R 8) [66,12,129,288,96,128] 13 := by
  apply FastRouting.sound _ _ [66,12,129,288,96,128] 13 (by decide) (choices 1) [1,16,32] r2856 c2856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u369
  · exact u370
  · exact u371

def b2857 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 133 296 176 33 112 240 368), lower := (rows 67 14 133 296 176 33 64 128 256), losses := [] }

theorem u2857 : Upper (D 8) (R 8) [66,12,129,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2858 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 14 133 296 176 48 97 225 353), lower := (rows 67 14 133 296 176 48 64 128 256), losses := [] }

theorem u2858 : Upper (D 8) (R 8) [66,12,129,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2858 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2859 : PairBound 9 := { available := 49, camps := [], pairs := [(4,0)], upper := (rows 67 14 133 296 176 96 113 177 305), lower := (rows 67 14 133 296 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 97 64 128 256), good := (rows 98 30 180 296 176 96 96 128 256) }] }

theorem u2859 : Upper (D 8) (R 8) [66,12,129,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2860 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 133 296 208 33 112 176 304), lower := (rows 67 14 133 296 208 33 64 128 256), losses := [] }

theorem u2860 : Upper (D 8) (R 8) [66,12,129,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2861 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 14 133 296 208 48 97 161 289), lower := (rows 67 14 133 296 208 48 64 128 256), losses := [] }

theorem u2861 : Upper (D 8) (R 8) [66,12,129,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2861 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2862 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 148 296 49 33 224 224 480), lower := (rows 67 14 148 296 49 33 64 128 256), losses := [] }

theorem u2862 : Upper (D 8) (R 8) [66,12,144,288,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2863 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 148 296 49 96 225 161 417), lower := (rows 67 14 148 296 49 96 64 128 256), losses := [] }

theorem u2863 : Upper (D 8) (R 8) [66,12,144,288,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2864 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 67 14 148 296 49 160 97 225 353), lower := (rows 67 14 148 296 49 160 64 128 256), losses := [] }

theorem u2864 : Upper (D 8) (R 8) [66,12,144,288,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2865 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 164 265 112 33 240 176 432), lower := (rows 67 14 164 265 112 33 64 128 256), losses := [] }

theorem u2865 : Upper (D 8) (R 8) [66,12,160,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2866 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 14 164 265 112 48 225 161 417), lower := (rows 67 14 164 265 112 48 64 128 256), losses := [] }

theorem u2866 : Upper (D 8) (R 8) [66,12,160,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2866 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2867 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 164 265 112 160 113 177 305), lower := (rows 67 14 164 265 112 160 64 128 256), losses := [] }

theorem u2867 : Upper (D 8) (R 8) [66,12,160,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2868 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 164 265 208 33 112 176 304), lower := (rows 67 14 164 265 208 33 64 128 256), losses := [] }

theorem u2868 : Upper (D 8) (R 8) [66,12,160,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2869 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 14 164 265 208 48 97 161 289), lower := (rows 67 14 164 265 208 48 64 128 256), losses := [] }

theorem u2869 : Upper (D 8) (R 8) [66,12,160,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2869 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2870 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 164 280 49 33 224 224 480), lower := (rows 67 14 164 280 49 33 64 128 256), losses := [] }

theorem u2870 : Upper (D 8) (R 8) [66,12,160,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2871 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 164 280 49 96 225 161 417), lower := (rows 67 14 164 280 49 96 64 128 256), losses := [] }

theorem u2871 : Upper (D 8) (R 8) [66,12,160,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2872 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 164 280 49 160 97 225 353), lower := (rows 67 14 164 280 49 160 64 128 256), losses := [] }

theorem u2872 : Upper (D 8) (R 8) [66,12,160,272,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2873 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 164 296 49 33 208 208 464), lower := (rows 67 14 164 296 49 33 64 128 256), losses := [] }

theorem u2873 : Upper (D 8) (R 8) [66,12,160,288,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2874 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 14 164 296 49 48 193 193 449), lower := (rows 67 14 164 296 49 48 64 128 256), losses := [] }

theorem u2874 : Upper (D 8) (R 8) [66,12,160,288,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2874 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2875 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 164 296 49 96 209 145 401), lower := (rows 67 14 164 296 49 96 64 128 256), losses := [] }

theorem u2875 : Upper (D 8) (R 8) [66,12,160,288,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2876 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 164 296 49 160 81 209 337), lower := (rows 67 14 164 296 49 160 64 128 256), losses := [] }

theorem u2876 : Upper (D 8) (R 8) [66,12,160,288,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2877 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 14 164 296 112 33 209 145 401), lower := (rows 67 14 164 296 112 33 64 128 256), losses := [] }

theorem u2877 : Upper (D 8) (R 8) [66,12,160,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2878 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 14 164 296 112 48 193 129 385), lower := (rows 67 14 164 296 112 48 64 128 256), losses := [] }

theorem u2878 : Upper (D 8) (R 8) [66,12,160,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2878 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2879 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 164 296 112 160 81 145 273), lower := (rows 67 14 164 296 112 160 64 128 256), losses := [] }

theorem u2879 : Upper (D 8) (R 8) [66,12,160,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2879
end Delivery.IrregularNine14.P08
