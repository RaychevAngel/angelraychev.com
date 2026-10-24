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

def b2940 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 196 73 274 48 96 133 261), lower := (rows 11 38 196 73 274 48 96 128 256), losses := [] }

theorem u2940 : Upper (D 6) (R 6) [10,36,192,65,258,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2940 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2941 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 38 196 73 276 34 65 176 304), lower := (rows 11 38 196 73 276 34 65 128 256), losses := [] }

theorem u2941 : Upper (D 6) (R 6) [10,36,192,65,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2942 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 38 196 73 276 34 80 161 289), lower := (rows 11 38 196 73 276 34 80 128 256), losses := [] }

theorem u2942 : Upper (D 6) (R 6) [10,36,192,65,260,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2942 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2943 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 404, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 196 73 276 34 96 145 273), lower := (rows 11 38 196 73 276 34 96 128 256), losses := [] }

theorem u2943 : Upper (D 6) (R 6) [10,36,192,65,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2944 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 38 196 73 304 34 65 148 276), lower := (rows 11 38 196 73 304 34 65 128 256), losses := [] }

theorem u2944 : Upper (D 6) (R 6) [10,36,192,65,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2945 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 304, targets := 68 },{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(4,2),(4,6)], upper := (rows 11 38 196 73 304 34 68 145 273), lower := (rows 11 38 196 73 304 34 68 128 256), losses := [] }

theorem u2945 : Upper (D 6) (R 6) [10,36,192,65,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2946 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 38 196 73 304 34 80 133 261), lower := (rows 11 38 196 73 304 34 80 128 256), losses := [] }

theorem u2946 : Upper (D 6) (R 6) [10,36,192,65,288,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2946 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2947 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 38 196 88 273 34 65 164 292), lower := (rows 11 38 196 88 273 34 65 128 256), losses := [] }

theorem u2947 : Upper (D 6) (R 6) [10,36,192,80,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2948 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 68 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 11 38 196 88 273 34 68 161 289), lower := (rows 11 38 196 88 273 34 68 128 256), losses := [] }

theorem u2948 : Upper (D 6) (R 6) [10,36,192,80,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2949 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 196 88 273 34 96 133 261), lower := (rows 11 38 196 88 273 34 96 128 256), losses := [] }

theorem u2949 : Upper (D 6) (R 6) [10,36,192,80,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2950 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 196 88 274 33 65 164 292), lower := (rows 11 38 196 88 274 33 65 128 256), losses := [] }

theorem u2950 : Upper (D 6) (R 6) [10,36,192,80,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2951 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 196 88 274 33 68 161 289), lower := (rows 11 38 196 88 274 33 68 128 256), losses := [] }

theorem u2951 : Upper (D 6) (R 6) [10,36,192,80,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2952 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 105, targets := 4 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 11 38 196 88 274 33 96 133 261), lower := (rows 11 38 196 88 274 33 96 128 256), losses := [] }

theorem u2952 : Upper (D 6) (R 6) [10,36,192,80,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2953 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 65 }], pairs := [(1,6),(4,0),(4,6)], upper := (rows 11 38 196 88 276 33 65 162 290), lower := (rows 11 38 196 88 276 33 65 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 22 97 0 135 263), good := (rows 443 438 438 56 406 417 417 128 256) }] }

theorem u2953 : Upper (D 6) (R 6) [10,36,192,80,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2954 : PairBound 9 := { available := 33, camps := [], pairs := [(3,1),(4,1),(4,6)], upper := (rows 11 38 196 88 276 33 66 161 289), lower := (rows 11 38 196 88 276 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 72 18 33 64 161 289), good := (rows 441 436 204 88 276 417 88 128 256) },{ target := 6, region := (rows 1 2 4 8 18 33 0 161 289), good := (rows 443 438 132 24 276 417 18 128 256) }] }

theorem u2954 : Upper (D 6) (R 6) [10,36,192,80,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2955 : Route 9 := (fun mask => (mask,id))

def c2955 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2955 : Upper (D 6) (R 6) [10,36,192,80,260,1,32] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,260,1,32] 13 (by decide) (choices 1) [1,2] r2955 c2955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u206
  · exact u207

def b2956 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,6)], upper := (rows 11 38 196 88 304 33 65 134 262), lower := (rows 11 38 196 88 304 33 65 128 256), losses := [] }

theorem u2956 : Upper (D 6) (R 6) [10,36,192,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2957 : Route 9 := (fun mask => (mask,id))

def c2957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2957 : Upper (D 6) (R 6) [10,36,192,80,288,1,2] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,288,1,2] 13 (by decide) (choices 1) [1,4] r2957 c2957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u208
  · exact u209

def b2958 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 196 88 304 33 68 131 259), lower := (rows 11 38 196 88 304 33 68 128 256), losses := [] }

theorem u2958 : Upper (D 6) (R 6) [10,36,192,80,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2959 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 196 104 273 33 66 148 276), lower := (rows 11 38 196 104 273 33 66 128 256), losses := [] }

theorem u2959 : Upper (D 6) (R 6) [10,36,192,96,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2960 : PairBound 9 := { available := 18, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 196 104 273 33 68 146 274), lower := (rows 11 38 196 104 273 33 68 128 256), losses := [] }

theorem u2960 : Upper (D 6) (R 6) [10,36,192,96,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2961 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 104 273 33 80 134 262), lower := (rows 11 38 196 104 273 33 80 128 256), losses := [] }

theorem u2961 : Upper (D 6) (R 6) [10,36,192,96,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2961 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2962 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 272, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 196 104 274 33 65 148 276), lower := (rows 11 38 196 104 274 33 65 128 256), losses := [] }

theorem u2962 : Upper (D 6) (R 6) [10,36,192,96,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2963 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 196 104 274 33 68 145 273), lower := (rows 11 38 196 104 274 33 68 128 256), losses := [] }

theorem u2963 : Upper (D 6) (R 6) [10,36,192,96,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2964 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 104 274 33 80 133 261), lower := (rows 11 38 196 104 274 33 80 128 256), losses := [] }

theorem u2964 : Upper (D 6) (R 6) [10,36,192,96,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2964 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2965 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 272, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 196 104 276 33 65 146 274), lower := (rows 11 38 196 104 276 33 65 128 256), losses := [] }

theorem u2965 : Upper (D 6) (R 6) [10,36,192,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2966 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 196 104 276 33 66 145 273), lower := (rows 11 38 196 104 276 33 66 128 256), losses := [] }

theorem u2966 : Upper (D 6) (R 6) [10,36,192,96,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2967 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 104 276 33 80 131 259), lower := (rows 11 38 196 104 276 33 80 128 256), losses := [] }

theorem u2967 : Upper (D 6) (R 6) [10,36,192,96,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2967 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2968 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 2 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 38 196 280 81 33 66 164 292), lower := (rows 11 38 196 280 81 33 66 128 256), losses := [] }

theorem u2968 : Upper (D 6) (R 6) [10,36,192,272,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2969 : PairBound 9 := { available := 34, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 196 280 81 33 68 162 290), lower := (rows 11 38 196 280 81 33 68 128 256), losses := [] }

theorem u2969 : Upper (D 6) (R 6) [10,36,192,272,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2970 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 196 280 81 33 96 134 262), lower := (rows 11 38 196 280 81 33 96 128 256), losses := [] }

theorem u2970 : Upper (D 6) (R 6) [10,36,192,272,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2971 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 38 196 280 81 34 65 164 292), lower := (rows 11 38 196 280 81 34 65 128 256), losses := [] }

theorem u2971 : Upper (D 6) (R 6) [10,36,192,272,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2972 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 102, targets := 1 },{ cop := 7, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 38 196 280 81 34 68 161 289), lower := (rows 11 38 196 280 81 34 68 128 256), losses := [] }

theorem u2972 : Upper (D 6) (R 6) [10,36,192,272,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2973 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 396, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 196 280 81 34 96 133 261), lower := (rows 11 38 196 280 81 34 96 128 256), losses := [] }

theorem u2973 : Upper (D 6) (R 6) [10,36,192,272,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2974 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 38 196 280 82 33 65 164 292), lower := (rows 11 38 196 280 82 33 65 128 256), losses := [] }

theorem u2974 : Upper (D 6) (R 6) [10,36,192,272,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2975 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 297, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 196 280 82 33 68 161 289), lower := (rows 11 38 196 280 82 33 68 128 256), losses := [] }

theorem u2975 : Upper (D 6) (R 6) [10,36,192,272,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2976 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 38 196 280 82 33 96 133 261), lower := (rows 11 38 196 280 82 33 96 128 256), losses := [] }

theorem u2976 : Upper (D 6) (R 6) [10,36,192,272,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2977 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 38 196 280 112 33 65 134 262), lower := (rows 11 38 196 280 112 33 65 128 256), losses := [] }

theorem u2977 : Upper (D 6) (R 6) [10,36,192,272,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2978 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,2)], upper := (rows 11 38 196 280 112 33 66 133 261), lower := (rows 11 38 196 280 112 33 66 128 256), losses := [] }

theorem u2978 : Upper (D 6) (R 6) [10,36,192,272,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2979 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 196 280 112 33 68 131 259), lower := (rows 11 38 196 280 112 33 68 128 256), losses := [] }

theorem u2979 : Upper (D 6) (R 6) [10,36,192,272,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2980 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 132, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 38 196 296 81 33 66 148 276), lower := (rows 11 38 196 296 81 33 66 128 256), losses := [] }

theorem u2980 : Upper (D 6) (R 6) [10,36,192,288,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2981 : PairBound 9 := { available := 18, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 196 296 81 33 68 146 274), lower := (rows 11 38 196 296 81 33 68 128 256), losses := [] }

theorem u2981 : Upper (D 6) (R 6) [10,36,192,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2982 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 196 296 81 33 80 134 262), lower := (rows 11 38 196 296 81 33 80 128 256), losses := [] }

theorem u2982 : Upper (D 6) (R 6) [10,36,192,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2982 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2983 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 132, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 196 296 82 33 65 148 276), lower := (rows 11 38 196 296 82 33 65 128 256), losses := [] }

theorem u2983 : Upper (D 6) (R 6) [10,36,192,288,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2984 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 297, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 196 296 82 33 68 145 273), lower := (rows 11 38 196 296 82 33 68 128 256), losses := [] }

theorem u2984 : Upper (D 6) (R 6) [10,36,192,288,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2985 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 38 196 296 82 33 80 133 261), lower := (rows 11 38 196 296 82 33 80 128 256), losses := [] }

theorem u2985 : Upper (D 6) (R 6) [10,36,192,288,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2985 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2986 : Route 9 := (fun mask => (mask,id))

def c2986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2986 : Upper (D 6) (R 6) [10,36,192,320,5,1,2] 13 := by
  apply FastRouting.sound _ _ [10,36,192,320,5,1,2] 13 (by decide) (choices 1) [16,32] r2986 c2986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u210
  · exact u211

def b2987 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(3,2)], upper := (rows 11 38 196 328 21 33 80 162 290), lower := (rows 11 38 196 328 21 33 80 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 49 80 131 259), good := (rows 427 418 192 328 505 417 120 128 256) }] }

theorem u2987 : Upper (D 6) (R 6) [10,36,192,320,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2987 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2988 : Route 9 := (fun mask => (mask,id))

def c2988 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2988 : Upper (D 6) (R 6) [10,36,192,320,5,1,32] 13 := by
  apply FastRouting.sound _ _ [10,36,192,320,5,1,32] 13 (by decide) (choices 1) [2,16] r2988 c2988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u212
  · exact u213

def b2989 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 388 25 84 96 65 162 290), lower := (rows 11 38 388 25 84 96 65 128 256), losses := [] }

theorem u2989 : Upper (D 6) (R 6) [10,36,384,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2990 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 388 25 84 96 66 161 289), lower := (rows 11 38 388 25 84 96 66 128 256), losses := [] }

theorem u2990 : Upper (D 6) (R 6) [10,36,384,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2991 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 388, targets := 96 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(2,6)], upper := (rows 11 38 388 25 84 96 96 131 259), lower := (rows 11 38 388 25 84 96 96 128 256), losses := [] }

theorem u2991 : Upper (D 6) (R 6) [10,36,384,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2992 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 388 28 81 96 65 162 290), lower := (rows 11 38 388 28 81 96 65 128 256), losses := [] }

theorem u2992 : Upper (D 6) (R 6) [10,36,384,20,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2993 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 388 28 81 96 66 161 289), lower := (rows 11 38 388 28 81 96 66 128 256), losses := [] }

theorem u2993 : Upper (D 6) (R 6) [10,36,384,20,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2994 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 388, targets := 96 },{ cop := 0, region := 112, targets := 2 }], pairs := [(2,5),(2,6),(4,1)], upper := (rows 11 38 388 28 81 96 96 131 259), lower := (rows 11 38 388 28 81 96 96 128 256), losses := [] }

theorem u2994 : Upper (D 6) (R 6) [10,36,384,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2995 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 388 73 21 96 66 176 304), lower := (rows 11 38 388 73 21 96 66 128 256), losses := [] }

theorem u2995 : Upper (D 6) (R 6) [10,36,384,65,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2996 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 38 388 73 21 96 80 162 290), lower := (rows 11 38 388 73 21 96 80 128 256), losses := [] }

theorem u2996 : Upper (D 6) (R 6) [10,36,384,65,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2996 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2997 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 38 388 73 21 96 96 146 274), lower := (rows 11 38 388 73 21 96 96 128 256), losses := [] }

theorem u2997 : Upper (D 6) (R 6) [10,36,384,65,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2998 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 388 73 84 34 65 176 304), lower := (rows 11 38 388 73 84 34 65 128 256), losses := [] }

theorem u2998 : Upper (D 6) (R 6) [10,36,384,65,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2999 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 388 73 84 34 80 161 289), lower := (rows 11 38 388 73 84 34 80 128 256), losses := [] }

theorem u2999 : Upper (D 6) (R 6) [10,36,384,65,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2999 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2999
end Delivery.IrregularNine14.P06
