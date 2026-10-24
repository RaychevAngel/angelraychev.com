import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2940 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 41 208 160 72 146 274), lower := (rows 7 290 69 41 208 160 72 128 256), losses := [] }

theorem u2940 : Upper (D 7) (R 7) [6,288,65,33,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2940 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2941 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 69 41 208 160 80 138 266), lower := (rows 7 290 69 41 208 160 80 128 256), losses := [] }

theorem u2941 : Upper (D 7) (R 7) [6,288,65,33,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2941 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2942 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 290 69 56 145 96 66 136 392), lower := (rows 7 290 69 56 145 96 66 128 256), losses := [] }

theorem u2942 : Upper (D 7) (R 7) [6,288,65,48,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2943 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 108, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 7 290 69 56 145 96 72 130 386), lower := (rows 7 290 69 56 145 96 72 128 256), losses := [] }

theorem u2943 : Upper (D 7) (R 7) [6,288,65,48,129,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2943 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2944 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 108, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(3,1)], upper := (rows 7 290 69 56 145 96 192 138 266), lower := (rows 7 290 69 56 145 96 192 128 256), losses := [] }

theorem u2944 : Upper (D 7) (R 7) [6,288,65,48,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2945 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 56 146 33 72 192 448), lower := (rows 7 290 69 56 146 33 72 128 256), losses := [] }

theorem u2945 : Upper (D 7) (R 7) [6,288,65,48,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2945 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2946 : PairBound 9 := { available := 72, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 290 69 56 146 33 192 200 328), lower := (rows 7 290 69 56 146 33 192 128 256), losses := [] }

theorem u2946 : Upper (D 7) (R 7) [6,288,65,48,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2947 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 290 69 56 146 96 65 136 392), lower := (rows 7 290 69 56 146 96 65 128 256), losses := [] }

theorem u2947 : Upper (D 7) (R 7) [6,288,65,48,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2948 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 56 146 96 72 129 385), lower := (rows 7 290 69 56 146 96 72 128 256), losses := [] }

theorem u2948 : Upper (D 7) (R 7) [6,288,65,48,130,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2948 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2949 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(3,1)], upper := (rows 7 290 69 56 146 96 192 137 265), lower := (rows 7 290 69 56 146 96 192 128 256), losses := [] }

theorem u2949 : Upper (D 7) (R 7) [6,288,65,48,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2950 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 290 69 56 152 96 65 130 386), lower := (rows 7 290 69 56 152 96 65 128 256), losses := [] }

theorem u2950 : Upper (D 7) (R 7) [6,288,65,48,136,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2951 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 290 69 56 152 96 66 129 385), lower := (rows 7 290 69 56 152 96 66 128 256), losses := [] }

theorem u2951 : Upper (D 7) (R 7) [6,288,65,48,136,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2952 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 290 69 56 152 96 192 131 259), lower := (rows 7 290 69 56 152 96 192 128 256), losses := [] }

theorem u2952 : Upper (D 7) (R 7) [6,288,65,48,136,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2953 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 290 69 56 208 34 65 136 392), lower := (rows 7 290 69 56 208 34 65 128 256), losses := [] }

theorem u2953 : Upper (D 7) (R 7) [6,288,65,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2954 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7)], upper := (rows 7 290 69 56 208 34 72 129 385), lower := (rows 7 290 69 56 208 34 72 128 256), losses := [] }

theorem u2954 : Upper (D 7) (R 7) [6,288,65,48,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2954 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2955 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 69 56 208 34 192 137 265), lower := (rows 7 290 69 56 208 34 192 128 256), losses := [] }

theorem u2955 : Upper (D 7) (R 7) [6,288,65,48,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2956 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 88 145 160 66 168 296), lower := (rows 7 290 69 88 145 160 66 128 256), losses := [] }

theorem u2956 : Upper (D 7) (R 7) [6,288,65,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2957 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 7 290 69 88 145 160 72 162 290), lower := (rows 7 290 69 88 145 160 72 128 256), losses := [] }

theorem u2957 : Upper (D 7) (R 7) [6,288,65,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2957 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2958 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 7 290 69 88 145 160 96 138 266), lower := (rows 7 290 69 88 145 160 96 128 256), losses := [] }

theorem u2958 : Upper (D 7) (R 7) [6,288,65,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2959 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 290 69 88 146 33 72 160 416), lower := (rows 7 290 69 88 146 33 72 128 256), losses := [] }

theorem u2959 : Upper (D 7) (R 7) [6,288,65,80,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2959 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2960 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 69 88 146 33 96 136 392), lower := (rows 7 290 69 88 146 33 96 128 256), losses := [] }

theorem u2960 : Upper (D 7) (R 7) [6,288,65,80,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2961 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 290 69 88 146 33 192 168 296), lower := (rows 7 290 69 88 146 33 192 128 256), losses := [] }

theorem u2961 : Upper (D 7) (R 7) [6,288,65,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2962 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 88 146 40 65 160 416), lower := (rows 7 290 69 88 146 40 65 128 256), losses := [] }

theorem u2962 : Upper (D 7) (R 7) [6,288,65,80,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2962 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2963 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 88 146 40 96 129 385), lower := (rows 7 290 69 88 146 40 96 128 256), losses := [] }

theorem u2963 : Upper (D 7) (R 7) [6,288,65,80,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2963 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2964 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 69 88 146 40 192 161 289), lower := (rows 7 290 69 88 146 40 192 128 256), losses := [] }

theorem u2964 : Upper (D 7) (R 7) [6,288,65,80,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2964 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2965 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 88 146 160 65 168 296), lower := (rows 7 290 69 88 146 160 65 128 256), losses := [] }

theorem u2965 : Upper (D 7) (R 7) [6,288,65,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2966 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 88 146 160 72 161 289), lower := (rows 7 290 69 88 146 160 72 128 256), losses := [] }

theorem u2966 : Upper (D 7) (R 7) [6,288,65,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2966 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2967 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 104, targets := 3 }], pairs := [(0,7),(2,7),(3,0),(3,1)], upper := (rows 7 290 69 88 146 160 96 137 265), lower := (rows 7 290 69 88 146 160 96 128 256), losses := [] }

theorem u2967 : Upper (D 7) (R 7) [6,288,65,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2968 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 290 69 88 176 33 66 136 392), lower := (rows 7 290 69 88 176 33 66 128 256), losses := [] }

theorem u2968 : Upper (D 7) (R 7) [6,288,65,80,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2969 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 290 69 88 176 33 72 130 386), lower := (rows 7 290 69 88 176 33 72 128 256), losses := [] }

theorem u2969 : Upper (D 7) (R 7) [6,288,65,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2969 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2970 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 290 69 88 176 33 192 138 266), lower := (rows 7 290 69 88 176 33 192 128 256), losses := [] }

theorem u2970 : Upper (D 7) (R 7) [6,288,65,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2971 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 290 69 88 176 34 65 136 392), lower := (rows 7 290 69 88 176 34 65 128 256), losses := [] }

theorem u2971 : Upper (D 7) (R 7) [6,288,65,80,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2972 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 290 69 88 176 34 72 129 385), lower := (rows 7 290 69 88 176 34 72 128 256), losses := [] }

theorem u2972 : Upper (D 7) (R 7) [6,288,65,80,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2972 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2973 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 290 69 88 176 34 192 137 265), lower := (rows 7 290 69 88 176 34 192 128 256), losses := [] }

theorem u2973 : Upper (D 7) (R 7) [6,288,65,80,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2974 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 69 88 176 40 65 130 386), lower := (rows 7 290 69 88 176 40 65 128 256), losses := [] }

theorem u2974 : Upper (D 7) (R 7) [6,288,65,80,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2974 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2975 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 88 176 40 66 129 385), lower := (rows 7 290 69 88 176 40 66 128 256), losses := [] }

theorem u2975 : Upper (D 7) (R 7) [6,288,65,80,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2975 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2976 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 290 69 88 176 40 192 131 259), lower := (rows 7 290 69 88 176 40 192 128 256), losses := [] }

theorem u2976 : Upper (D 7) (R 7) [6,288,65,80,160,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2976 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2977 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 104 145 160 66 152 280), lower := (rows 7 290 69 104 145 160 66 128 256), losses := [] }

theorem u2977 : Upper (D 7) (R 7) [6,288,65,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2978 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 104 145 160 72 146 274), lower := (rows 7 290 69 104 145 160 72 128 256), losses := [] }

theorem u2978 : Upper (D 7) (R 7) [6,288,65,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2978 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2979 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 69 104 145 160 80 138 266), lower := (rows 7 290 69 104 145 160 80 128 256), losses := [] }

theorem u2979 : Upper (D 7) (R 7) [6,288,65,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2979 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2980 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 69 104 146 48 65 136 392), lower := (rows 7 290 69 104 146 48 65 128 256), losses := [] }

theorem u2980 : Upper (D 7) (R 7) [6,288,65,96,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2980 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2981 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 290 69 104 146 48 72 129 385), lower := (rows 7 290 69 104 146 48 72 128 256), losses := [] }

theorem u2981 : Upper (D 7) (R 7) [6,288,65,96,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2981 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2982 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 69 104 146 48 192 137 265), lower := (rows 7 290 69 104 146 48 192 128 256), losses := [] }

theorem u2982 : Upper (D 7) (R 7) [6,288,65,96,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2982 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2983 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 290 69 104 146 160 65 152 280), lower := (rows 7 290 69 104 146 160 65 128 256), losses := [] }

theorem u2983 : Upper (D 7) (R 7) [6,288,65,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2984 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 104 146 160 72 145 273), lower := (rows 7 290 69 104 146 160 72 128 256), losses := [] }

theorem u2984 : Upper (D 7) (R 7) [6,288,65,96,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2984 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2985 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 104 146 160 80 137 265), lower := (rows 7 290 69 104 146 160 80 128 256), losses := [] }

theorem u2985 : Upper (D 7) (R 7) [6,288,65,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2985 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2986 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 69 104 152 48 65 130 386), lower := (rows 7 290 69 104 152 48 65 128 256), losses := [] }

theorem u2986 : Upper (D 7) (R 7) [6,288,65,96,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2986 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2987 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 69 104 152 48 66 129 385), lower := (rows 7 290 69 104 152 48 66 128 256), losses := [] }

theorem u2987 : Upper (D 7) (R 7) [6,288,65,96,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2987 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2988 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 290 69 104 152 48 192 131 259), lower := (rows 7 290 69 104 152 48 192 128 256), losses := [] }

theorem u2988 : Upper (D 7) (R 7) [6,288,65,96,136,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2988 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2989 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 290 69 104 152 160 65 146 274), lower := (rows 7 290 69 104 152 160 65 128 256), losses := [] }

theorem u2989 : Upper (D 7) (R 7) [6,288,65,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2990 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 104 152 160 66 145 273), lower := (rows 7 290 69 104 152 160 66 128 256), losses := [] }

theorem u2990 : Upper (D 7) (R 7) [6,288,65,96,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2991 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 290 69 104 152 160 80 131 259), lower := (rows 7 290 69 104 152 160 80 128 256), losses := [] }

theorem u2991 : Upper (D 7) (R 7) [6,288,65,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2991 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2992 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 290 69 137 146 40 80 224 352), lower := (rows 7 290 69 137 146 40 80 128 256), losses := [] }

theorem u2992 : Upper (D 7) (R 7) [6,288,65,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2992 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2993 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 290 69 137 146 40 96 208 336), lower := (rows 7 290 69 137 146 40 96 128 256), losses := [] }

theorem u2993 : Upper (D 7) (R 7) [6,288,65,129,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2993 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2994 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 290 69 137 146 48 72 224 352), lower := (rows 7 290 69 137 146 48 72 128 256), losses := [] }

theorem u2994 : Upper (D 7) (R 7) [6,288,65,129,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2994 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2995 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 136, targets := 2 }], pairs := [(0,7),(2,7),(3,1)], upper := (rows 7 290 69 137 146 48 96 200 328), lower := (rows 7 290 69 137 146 48 96 128 256), losses := [] }

theorem u2995 : Upper (D 7) (R 7) [6,288,65,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2995 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2996 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 69 137 146 96 72 176 304), lower := (rows 7 290 69 137 146 96 72 128 256), losses := [] }

theorem u2996 : Upper (D 7) (R 7) [6,288,65,129,130,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2996 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2997 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 69 137 146 96 80 168 296), lower := (rows 7 290 69 137 146 96 80 128 256), losses := [] }

theorem u2997 : Upper (D 7) (R 7) [6,288,65,129,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2997 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2998 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 290 69 137 146 96 96 152 280), lower := (rows 7 290 69 137 146 96 96 128 256), losses := [] }

theorem u2998 : Upper (D 7) (R 7) [6,288,65,129,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2999 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 290 69 137 176 96 66 152 280), lower := (rows 7 290 69 137 176 96 66 128 256), losses := [] }

theorem u2999 : Upper (D 7) (R 7) [6,288,65,129,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2999
end Delivery.IrregularNine14.P07
