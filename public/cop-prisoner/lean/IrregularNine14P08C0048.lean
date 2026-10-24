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

def r2880 : Route 9 := (fun mask => (mask,id))

def c2880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2880 : Upper (D 8) (R 8) [66,12,160,288,192,1] 13 := by
  apply FastRouting.sound _ _ [66,12,160,288,192,1] 13 (by decide) (choices 1) [1,16,32] r2880 c2880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u372
  · exact u373
  · exact u374

def b2881 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 14 164 296 208 48 97 161 289), lower := (rows 67 14 164 296 208 48 64 128 256), losses := [] }

theorem u2881 : Upper (D 8) (R 8) [66,12,160,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2881 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2882 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 44 400 33 224 224 480), lower := (rows 67 35 28 44 400 33 64 128 256), losses := [] }

theorem u2882 : Upper (D 8) (R 8) [66,33,24,36,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2883 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 28 44 400 96 225 161 417), lower := (rows 67 35 28 44 400 96 64 128 256), losses := [] }

theorem u2883 : Upper (D 8) (R 8) [66,33,24,36,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2884 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 44, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 44 400 160 97 225 353), lower := (rows 67 35 28 44 400 160 64 128 256), losses := [] }

theorem u2884 : Upper (D 8) (R 8) [66,33,24,36,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2885 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 140 304 33 224 224 480), lower := (rows 67 35 28 140 304 33 64 128 256), losses := [] }

theorem u2885 : Upper (D 8) (R 8) [66,33,24,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2886 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 28 140 304 96 225 161 417), lower := (rows 67 35 28 140 304 96 64 128 256), losses := [] }

theorem u2886 : Upper (D 8) (R 8) [66,33,24,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2887 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 140 304 160 97 225 353), lower := (rows 67 35 28 140 304 160 64 128 256), losses := [] }

theorem u2887 : Upper (D 8) (R 8) [66,33,24,132,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2888 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 168 276 33 224 224 480), lower := (rows 67 35 28 168 276 33 64 128 256), losses := [] }

theorem u2888 : Upper (D 8) (R 8) [66,33,24,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2889 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 28 168 276 96 225 161 417), lower := (rows 67 35 28 168 276 96 64 128 256), losses := [] }

theorem u2889 : Upper (D 8) (R 8) [66,33,24,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2890 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 168 276 160 97 225 353), lower := (rows 67 35 28 168 276 160 64 128 256), losses := [] }

theorem u2890 : Upper (D 8) (R 8) [66,33,24,160,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2891 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 168 304 33 196 196 452), lower := (rows 67 35 28 168 304 33 64 128 256), losses := [] }

theorem u2891 : Upper (D 8) (R 8) [66,33,24,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2892 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 35 28 168 304 36 193 193 449), lower := (rows 67 35 28 168 304 36 64 128 256), losses := [] }

theorem u2892 : Upper (D 8) (R 8) [66,33,24,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2892 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2893 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 28 168 304 96 197 133 389), lower := (rows 67 35 28 168 304 96 64 128 256), losses := [] }

theorem u2893 : Upper (D 8) (R 8) [66,33,24,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2894 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 168 304 160 69 197 325), lower := (rows 67 35 28 168 304 160 64 128 256), losses := [] }

theorem u2894 : Upper (D 8) (R 8) [66,33,24,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2895 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 168 336 33 228 164 420), lower := (rows 67 35 28 168 336 33 64 128 256), losses := [] }

theorem u2895 : Upper (D 8) (R 8) [66,33,24,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2896 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 28 168 336 36 225 161 417), lower := (rows 67 35 28 168 336 36 64 128 256), losses := [] }

theorem u2896 : Upper (D 8) (R 8) [66,33,24,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2896 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2897 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 168 336 160 101 165 293), lower := (rows 67 35 28 168 336 160 64 128 256), losses := [] }

theorem u2897 : Upper (D 8) (R 8) [66,33,24,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2898 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 200 304 33 228 164 420), lower := (rows 67 35 28 200 304 33 64 128 256), losses := [] }

theorem u2898 : Upper (D 8) (R 8) [66,33,24,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2899 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 28 200 304 36 225 161 417), lower := (rows 67 35 28 200 304 36 64 128 256), losses := [] }

theorem u2899 : Upper (D 8) (R 8) [66,33,24,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2899 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2900 : Route 9 := (fun mask => (mask,id))

def c2900 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2900 : Upper (D 8) (R 8) [66,33,24,192,288,128] 13 := by
  apply FastRouting.sound _ _ [66,33,24,192,288,128] 13 (by decide) (choices 1) [1,4,32] r2900 c2900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u375
  · exact u376
  · exact u377

def b2901 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 88 176 33 452 388 388), lower := (rows 67 35 44 88 176 33 64 128 256), losses := [] }

theorem u2901 : Upper (D 8) (R 8) [66,33,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2902 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 67 35 44 88 176 36 449 385 385), lower := (rows 67 35 44 88 176 36 64 128 256), losses := [] }

theorem u2902 : Upper (D 8) (R 8) [66,33,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2902 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2903 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 88 176 160 325 389 261), lower := (rows 67 35 44 88 176 160 64 128 256), losses := [] }

theorem u2903 : Upper (D 8) (R 8) [66,33,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2904 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 35 44 88 176 288 197 133 389), lower := (rows 67 35 44 88 176 288 64 128 256), losses := [] }

theorem u2904 : Upper (D 8) (R 8) [66,33,40,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2904 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2905 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 88 304 33 196 132 388), lower := (rows 67 35 44 88 304 33 64 128 256), losses := [] }

theorem u2905 : Upper (D 8) (R 8) [66,33,40,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2906 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 35 44 88 304 36 193 129 385), lower := (rows 67 35 44 88 304 36 64 128 256), losses := [] }

theorem u2906 : Upper (D 8) (R 8) [66,33,40,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2906 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2907 : Route 9 := (fun mask => (mask,id))

def c2907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2907 : Upper (D 8) (R 8) [66,33,40,80,288,128] 13 := by
  apply FastRouting.sound _ _ [66,33,40,80,288,128] 13 (by decide) (choices 1) [1,4,128] r2907 c2907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u378
  · exact u379
  · exact u380

def b2908 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 88 400 33 228 164 420), lower := (rows 67 35 44 88 400 33 64 128 256), losses := [] }

theorem u2908 : Upper (D 8) (R 8) [66,33,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2909 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 44 88 400 36 225 161 417), lower := (rows 67 35 44 88 400 36 64 128 256), losses := [] }

theorem u2909 : Upper (D 8) (R 8) [66,33,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2909 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2910 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 88 400 160 101 165 293), lower := (rows 67 35 44 88 400 160 64 128 256), losses := [] }

theorem u2910 : Upper (D 8) (R 8) [66,33,40,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2911 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 140 304 33 208 208 464), lower := (rows 67 35 44 140 304 33 64 128 256), losses := [] }

theorem u2911 : Upper (D 8) (R 8) [66,33,40,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2912 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 35 44 140 304 48 193 193 449), lower := (rows 67 35 44 140 304 48 64 128 256), losses := [] }

theorem u2912 : Upper (D 8) (R 8) [66,33,40,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2912 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2913 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 44 140 304 96 209 145 401), lower := (rows 67 35 44 140 304 96 64 128 256), losses := [] }

theorem u2913 : Upper (D 8) (R 8) [66,33,40,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2914 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 140 304 160 81 209 337), lower := (rows 67 35 44 140 304 160 64 128 256), losses := [] }

theorem u2914 : Upper (D 8) (R 8) [66,33,40,132,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2915 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 140 336 33 240 176 432), lower := (rows 67 35 44 140 336 33 64 128 256), losses := [] }

theorem u2915 : Upper (D 8) (R 8) [66,33,40,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2916 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 44 140 336 48 225 161 417), lower := (rows 67 35 44 140 336 48 64 128 256), losses := [] }

theorem u2916 : Upper (D 8) (R 8) [66,33,40,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2916 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2917 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 140 336 160 113 177 305), lower := (rows 67 35 44 140 336 160 64 128 256), losses := [] }

theorem u2917 : Upper (D 8) (R 8) [66,33,40,132,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2918 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 152 276 33 224 224 480), lower := (rows 67 35 44 152 276 33 64 128 256), losses := [] }

theorem u2918 : Upper (D 8) (R 8) [66,33,40,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2919 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 44 152 276 96 225 161 417), lower := (rows 67 35 44 152 276 96 64 128 256), losses := [] }

theorem u2919 : Upper (D 8) (R 8) [66,33,40,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2920 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 152 276 160 97 225 353), lower := (rows 67 35 44 152 276 160 64 128 256), losses := [] }

theorem u2920 : Upper (D 8) (R 8) [66,33,40,144,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2921 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 152 304 33 196 196 452), lower := (rows 67 35 44 152 304 33 64 128 256), losses := [] }

theorem u2921 : Upper (D 8) (R 8) [66,33,40,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2922 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 35 44 152 304 36 193 193 449), lower := (rows 67 35 44 152 304 36 64 128 256), losses := [] }

theorem u2922 : Upper (D 8) (R 8) [66,33,40,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2922 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2923 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 44 152 304 96 197 133 389), lower := (rows 67 35 44 152 304 96 64 128 256), losses := [] }

theorem u2923 : Upper (D 8) (R 8) [66,33,40,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2924 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 152 304 160 69 197 325), lower := (rows 67 35 44 152 304 160 64 128 256), losses := [] }

theorem u2924 : Upper (D 8) (R 8) [66,33,40,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2925 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 152 336 33 228 164 420), lower := (rows 67 35 44 152 336 33 64 128 256), losses := [] }

theorem u2925 : Upper (D 8) (R 8) [66,33,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2926 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 44 152 336 36 225 161 417), lower := (rows 67 35 44 152 336 36 64 128 256), losses := [] }

theorem u2926 : Upper (D 8) (R 8) [66,33,40,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2926 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2927 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 152 336 160 101 165 293), lower := (rows 67 35 44 152 336 160 64 128 256), losses := [] }

theorem u2927 : Upper (D 8) (R 8) [66,33,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2928 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 200 176 33 340 404 276), lower := (rows 67 35 44 200 176 33 64 128 256), losses := [] }

theorem u2928 : Upper (D 8) (R 8) [66,33,40,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2929 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 67 35 44 200 176 36 337 401 273), lower := (rows 67 35 44 200 176 36 64 128 256), losses := [] }

theorem u2929 : Upper (D 8) (R 8) [66,33,40,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2929 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2930 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 67 35 44 200 176 48 325 389 261), lower := (rows 67 35 44 200 176 48 64 128 256), losses := [] }

theorem u2930 : Upper (D 8) (R 8) [66,33,40,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2930 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2931 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 67 35 44 200 176 288 85 149 277), lower := (rows 67 35 44 200 176 288 64 128 256), losses := [] }

theorem u2931 : Upper (D 8) (R 8) [66,33,40,192,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2931 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2932 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 200 276 33 240 176 432), lower := (rows 67 35 44 200 276 33 64 128 256), losses := [] }

theorem u2932 : Upper (D 8) (R 8) [66,33,40,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2933 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 44 200 276 48 225 161 417), lower := (rows 67 35 44 200 276 48 64 128 256), losses := [] }

theorem u2933 : Upper (D 8) (R 8) [66,33,40,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2933 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2934 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 200 276 160 113 177 305), lower := (rows 67 35 44 200 276 160 64 128 256), losses := [] }

theorem u2934 : Upper (D 8) (R 8) [66,33,40,192,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2935 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 200 304 33 212 148 404), lower := (rows 67 35 44 200 304 33 64 128 256), losses := [] }

theorem u2935 : Upper (D 8) (R 8) [66,33,40,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2936 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 35 44 200 304 36 209 145 401), lower := (rows 67 35 44 200 304 36 64 128 256), losses := [] }

theorem u2936 : Upper (D 8) (R 8) [66,33,40,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2936 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2937 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 35 44 200 304 48 197 133 389), lower := (rows 67 35 44 200 304 48 64 128 256), losses := [] }

theorem u2937 : Upper (D 8) (R 8) [66,33,40,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2937 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2938 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 200 304 160 85 149 277), lower := (rows 67 35 44 200 304 160 64 128 256), losses := [] }

theorem u2938 : Upper (D 8) (R 8) [66,33,40,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2939 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 200 400 33 116 180 308), lower := (rows 67 35 44 200 400 33 64 128 256), losses := [] }

theorem u2939 : Upper (D 8) (R 8) [66,33,40,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2939
end Delivery.IrregularNine14.P08
