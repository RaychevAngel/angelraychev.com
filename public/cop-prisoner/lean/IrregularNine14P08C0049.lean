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

def b2940 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 35 44 200 400 36 113 177 305), lower := (rows 67 35 44 200 400 36 64 128 256), losses := [] }

theorem u2940 : Upper (D 8) (R 8) [66,33,40,192,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2940 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2941 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 35 44 200 400 48 101 165 293), lower := (rows 67 35 44 200 400 48 64 128 256), losses := [] }

theorem u2941 : Upper (D 8) (R 8) [66,33,40,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2941 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2942 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 268 176 33 208 208 464), lower := (rows 67 35 44 268 176 33 64 128 256), losses := [] }

theorem u2942 : Upper (D 8) (R 8) [66,33,40,260,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2943 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 35 44 268 176 48 193 193 449), lower := (rows 67 35 44 268 176 48 64 128 256), losses := [] }

theorem u2943 : Upper (D 8) (R 8) [66,33,40,260,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2943 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2944 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 44 268 176 96 209 145 401), lower := (rows 67 35 44 268 176 96 64 128 256), losses := [] }

theorem u2944 : Upper (D 8) (R 8) [66,33,40,260,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2945 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 268 176 160 81 209 337), lower := (rows 67 35 44 268 176 160 64 128 256), losses := [] }

theorem u2945 : Upper (D 8) (R 8) [66,33,40,260,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2946 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 268 208 33 240 176 432), lower := (rows 67 35 44 268 208 33 64 128 256), losses := [] }

theorem u2946 : Upper (D 8) (R 8) [66,33,40,260,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2947 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 44 268 208 48 225 161 417), lower := (rows 67 35 44 268 208 48 64 128 256), losses := [] }

theorem u2947 : Upper (D 8) (R 8) [66,33,40,260,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2947 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2948 : Route 9 := (fun mask => (mask,id))

def c2948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2948 : Upper (D 8) (R 8) [66,33,40,260,192,128] 13 := by
  apply FastRouting.sound _ _ [66,33,40,260,192,128] 13 (by decide) (choices 1) [1,16,32] r2948 c2948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u381
  · exact u382
  · exact u383

def b2949 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 280 148 33 224 224 480), lower := (rows 67 35 44 280 148 33 64 128 256), losses := [] }

theorem u2949 : Upper (D 8) (R 8) [66,33,40,272,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2950 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 44 280 148 96 225 161 417), lower := (rows 67 35 44 280 148 96 64 128 256), losses := [] }

theorem u2950 : Upper (D 8) (R 8) [66,33,40,272,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2951 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 280 148 160 97 225 353), lower := (rows 67 35 44 280 148 160 64 128 256), losses := [] }

theorem u2951 : Upper (D 8) (R 8) [66,33,40,272,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2952 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 280 176 33 196 196 452), lower := (rows 67 35 44 280 176 33 64 128 256), losses := [] }

theorem u2952 : Upper (D 8) (R 8) [66,33,40,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2953 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 35 44 280 176 36 193 193 449), lower := (rows 67 35 44 280 176 36 64 128 256), losses := [] }

theorem u2953 : Upper (D 8) (R 8) [66,33,40,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2953 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2954 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 44 280 176 96 197 133 389), lower := (rows 67 35 44 280 176 96 64 128 256), losses := [] }

theorem u2954 : Upper (D 8) (R 8) [66,33,40,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2955 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 280 176 160 69 197 325), lower := (rows 67 35 44 280 176 160 64 128 256), losses := [] }

theorem u2955 : Upper (D 8) (R 8) [66,33,40,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2956 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 280 208 33 228 164 420), lower := (rows 67 35 44 280 208 33 64 128 256), losses := [] }

theorem u2956 : Upper (D 8) (R 8) [66,33,40,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2957 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 44 280 208 36 225 161 417), lower := (rows 67 35 44 280 208 36 64 128 256), losses := [] }

theorem u2957 : Upper (D 8) (R 8) [66,33,40,272,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2957 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2958 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 280 208 160 101 165 293), lower := (rows 67 35 44 280 208 160 64 128 256), losses := [] }

theorem u2958 : Upper (D 8) (R 8) [66,33,40,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2959 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 328 148 33 240 176 432), lower := (rows 67 35 44 328 148 33 64 128 256), losses := [] }

theorem u2959 : Upper (D 8) (R 8) [66,33,40,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2960 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 44 328 148 48 225 161 417), lower := (rows 67 35 44 328 148 48 64 128 256), losses := [] }

theorem u2960 : Upper (D 8) (R 8) [66,33,40,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2960 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2961 : Route 9 := (fun mask => (mask,id))

def c2961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2961 : Upper (D 8) (R 8) [66,33,40,320,132,128] 13 := by
  apply FastRouting.sound _ _ [66,33,40,320,132,128] 13 (by decide) (choices 1) [1,16,32] r2961 c2961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u384
  · exact u385
  · exact u386

def b2962 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 328 176 33 212 148 404), lower := (rows 67 35 44 328 176 33 64 128 256), losses := [] }

theorem u2962 : Upper (D 8) (R 8) [66,33,40,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2963 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 35 44 328 176 36 209 145 401), lower := (rows 67 35 44 328 176 36 64 128 256), losses := [] }

theorem u2963 : Upper (D 8) (R 8) [66,33,40,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2963 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2964 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 35 44 328 176 48 197 133 389), lower := (rows 67 35 44 328 176 48 64 128 256), losses := [] }

theorem u2964 : Upper (D 8) (R 8) [66,33,40,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2964 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2965 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 328 176 160 85 149 277), lower := (rows 67 35 44 328 176 160 64 128 256), losses := [] }

theorem u2965 : Upper (D 8) (R 8) [66,33,40,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2966 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 392 84 33 240 176 432), lower := (rows 67 35 44 392 84 33 64 128 256), losses := [] }

theorem u2966 : Upper (D 8) (R 8) [66,33,40,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2967 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 44 392 84 48 225 161 417), lower := (rows 67 35 44 392 84 48 64 128 256), losses := [] }

theorem u2967 : Upper (D 8) (R 8) [66,33,40,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2967 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2968 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 83, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 392 84 160 113 177 305), lower := (rows 67 35 44 392 84 160 64 128 256), losses := [] }

theorem u2968 : Upper (D 8) (R 8) [66,33,40,384,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2969 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 392 176 33 84 212 340), lower := (rows 67 35 44 392 176 33 64 128 256), losses := [] }

theorem u2969 : Upper (D 8) (R 8) [66,33,40,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2970 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 35 44 392 176 36 81 209 337), lower := (rows 67 35 44 392 176 36 64 128 256), losses := [] }

theorem u2970 : Upper (D 8) (R 8) [66,33,40,384,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2970 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2971 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 67 35 44 392 176 48 69 197 325), lower := (rows 67 35 44 392 176 48 64 128 256), losses := [] }

theorem u2971 : Upper (D 8) (R 8) [66,33,40,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2971 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2972 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 44 392 176 96 85 149 277), lower := (rows 67 35 44 392 176 96 64 128 256), losses := [] }

theorem u2972 : Upper (D 8) (R 8) [66,33,40,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2973 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 392 208 33 116 180 308), lower := (rows 67 35 44 392 208 33 64 128 256), losses := [] }

theorem u2973 : Upper (D 8) (R 8) [66,33,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2974 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 35 44 392 208 36 113 177 305), lower := (rows 67 35 44 392 208 36 64 128 256), losses := [] }

theorem u2974 : Upper (D 8) (R 8) [66,33,40,384,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2974 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2975 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 35 44 392 208 48 101 165 293), lower := (rows 67 35 44 392 208 48 64 128 256), losses := [] }

theorem u2975 : Upper (D 8) (R 8) [66,33,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2975 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2976 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 152 304 33 228 164 420), lower := (rows 67 35 76 152 304 33 64 128 256), losses := [] }

theorem u2976 : Upper (D 8) (R 8) [66,33,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2977 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 76 152 304 36 225 161 417), lower := (rows 67 35 76 152 304 36 64 128 256), losses := [] }

theorem u2977 : Upper (D 8) (R 8) [66,33,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2977 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2978 : Route 9 := (fun mask => (mask,id))

def c2978 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2978 : Upper (D 8) (R 8) [66,33,72,144,288,128] 13 := by
  apply FastRouting.sound _ _ [66,33,72,144,288,128] 13 (by decide) (choices 1) [1,4,32] r2978 c2978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u387
  · exact u388
  · exact u389

def b2979 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 168 276 33 240 176 432), lower := (rows 67 35 76 168 276 33 64 128 256), losses := [] }

theorem u2979 : Upper (D 8) (R 8) [66,33,72,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2980 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 76 168 276 48 225 161 417), lower := (rows 67 35 76 168 276 48 64 128 256), losses := [] }

theorem u2980 : Upper (D 8) (R 8) [66,33,72,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2980 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2981 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 168 276 160 113 177 305), lower := (rows 67 35 76 168 276 160 64 128 256), losses := [] }

theorem u2981 : Upper (D 8) (R 8) [66,33,72,160,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2982 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 168 304 33 212 148 404), lower := (rows 67 35 76 168 304 33 64 128 256), losses := [] }

theorem u2982 : Upper (D 8) (R 8) [66,33,72,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2983 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 35 76 168 304 36 209 145 401), lower := (rows 67 35 76 168 304 36 64 128 256), losses := [] }

theorem u2983 : Upper (D 8) (R 8) [66,33,72,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2983 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2984 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 35 76 168 304 48 197 133 389), lower := (rows 67 35 76 168 304 48 64 128 256), losses := [] }

theorem u2984 : Upper (D 8) (R 8) [66,33,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2984 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2985 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 168 304 160 85 149 277), lower := (rows 67 35 76 168 304 160 64 128 256), losses := [] }

theorem u2985 : Upper (D 8) (R 8) [66,33,72,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2986 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 168 400 33 116 180 308), lower := (rows 67 35 76 168 400 33 64 128 256), losses := [] }

theorem u2986 : Upper (D 8) (R 8) [66,33,72,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2987 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 35 76 168 400 36 113 177 305), lower := (rows 67 35 76 168 400 36 64 128 256), losses := [] }

theorem u2987 : Upper (D 8) (R 8) [66,33,72,160,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2987 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2988 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 35 76 168 400 48 101 165 293), lower := (rows 67 35 76 168 400 48 64 128 256), losses := [] }

theorem u2988 : Upper (D 8) (R 8) [66,33,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2988 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2989 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 280 176 33 228 164 420), lower := (rows 67 35 76 280 176 33 64 128 256), losses := [] }

theorem u2989 : Upper (D 8) (R 8) [66,33,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2990 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 76 280 176 36 225 161 417), lower := (rows 67 35 76 280 176 36 64 128 256), losses := [] }

theorem u2990 : Upper (D 8) (R 8) [66,33,72,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2990 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2991 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 280 176 160 101 165 293), lower := (rows 67 35 76 280 176 160 64 128 256), losses := [] }

theorem u2991 : Upper (D 8) (R 8) [66,33,72,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2992 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 296 148 33 240 176 432), lower := (rows 67 35 76 296 148 33 64 128 256), losses := [] }

theorem u2992 : Upper (D 8) (R 8) [66,33,72,288,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2993 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 35 76 296 148 48 225 161 417), lower := (rows 67 35 76 296 148 48 64 128 256), losses := [] }

theorem u2993 : Upper (D 8) (R 8) [66,33,72,288,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2993 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2994 : Route 9 := (fun mask => (mask,id))

def c2994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2994 : Upper (D 8) (R 8) [66,33,72,288,132,128] 13 := by
  apply FastRouting.sound _ _ [66,33,72,288,132,128] 13 (by decide) (choices 1) [1,16,32] r2994 c2994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u390
  · exact u391
  · exact u392

def b2995 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 296 176 33 212 148 404), lower := (rows 67 35 76 296 176 33 64 128 256), losses := [] }

theorem u2995 : Upper (D 8) (R 8) [66,33,72,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2996 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 35 76 296 176 36 209 145 401), lower := (rows 67 35 76 296 176 36 64 128 256), losses := [] }

theorem u2996 : Upper (D 8) (R 8) [66,33,72,288,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2996 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2997 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 35 76 296 176 48 197 133 389), lower := (rows 67 35 76 296 176 48 64 128 256), losses := [] }

theorem u2997 : Upper (D 8) (R 8) [66,33,72,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2997 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2998 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 296 176 160 85 149 277), lower := (rows 67 35 76 296 176 160 64 128 256), losses := [] }

theorem u2998 : Upper (D 8) (R 8) [66,33,72,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2999 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 76 392 176 33 116 180 308), lower := (rows 67 35 76 392 176 33 64 128 256), losses := [] }

theorem u2999 : Upper (D 8) (R 8) [66,33,72,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2999
end Delivery.IrregularNine14.P08
