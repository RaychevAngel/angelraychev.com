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

def b2940 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,5),(1,8),(4,5)], upper := (rows 97 131 140 296 336 36 65 146 274), lower := (rows 97 131 140 296 336 36 65 128 256), losses := [] }

theorem u2940 : Upper (D 9) (R 9) [96,129,136,288,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2940 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2941 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 280, targets := 128 }], pairs := [(1,5),(3,7),(4,5)], upper := (rows 97 131 140 296 336 36 66 145 273), lower := (rows 97 131 140 296 336 36 66 128 256), losses := [] }

theorem u2941 : Upper (D 9) (R 9) [96,129,136,288,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2941 [(5,2),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2942 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 140 296 336 36 80 131 259), lower := (rows 97 131 140 296 336 36 80 128 256), losses := [] }

theorem u2942 : Upper (D 9) (R 9) [96,129,136,288,320,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2942 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2943 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 131 164 265 336 36 66 152 280), lower := (rows 97 131 164 265 336 36 66 128 256), losses := [] }

theorem u2943 : Upper (D 9) (R 9) [96,129,160,257,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2943 [(5,2),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2944 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 404, targets := 1 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(2,0),(4,0)], upper := (rows 97 131 164 265 336 40 66 148 276), lower := (rows 97 131 164 265 336 40 66 128 256), losses := [] }

theorem u2944 : Upper (D 9) (R 9) [96,129,160,257,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2944 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2945 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 131 164 265 336 40 68 146 274), lower := (rows 97 131 164 265 336 40 68 128 256), losses := [] }

theorem u2945 : Upper (D 9) (R 9) [96,129,160,257,320,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2945 [(5,3),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2946 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 404, targets := 1 },{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7),(2,0),(4,0),(4,7)], upper := (rows 97 131 164 266 276 40 65 208 336), lower := (rows 97 131 164 266 276 40 65 128 256), losses := [] }

theorem u2946 : Upper (D 9) (R 9) [96,129,160,258,260,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2946 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2947 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 394, targets := 32 },{ cop := 0, region := 130, targets := 256 }], pairs := [(1,5),(1,8),(3,5)], upper := (rows 97 131 164 266 276 40 80 193 321), lower := (rows 97 131 164 266 276 40 80 128 256), losses := [] }

theorem u2947 : Upper (D 9) (R 9) [96,129,160,258,260,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2947 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2948 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 394, targets := 32 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,5),(1,8),(3,5)], upper := (rows 97 131 164 266 276 48 65 200 328), lower := (rows 97 131 164 266 276 48 65 128 256), losses := [] }

theorem u2948 : Upper (D 9) (R 9) [96,129,160,258,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2948 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2949 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 394, targets := 32 },{ cop := 0, region := 130, targets := 256 }], pairs := [(1,5),(1,8),(3,5)], upper := (rows 97 131 164 266 276 48 72 193 321), lower := (rows 97 131 164 266 276 48 72 128 256), losses := [] }

theorem u2949 : Upper (D 9) (R 9) [96,129,160,258,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2949 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2950 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 410, targets := 32 },{ cop := 7, region := 101, targets := 256 }], pairs := [(0,8),(1,5),(3,5),(4,5)], upper := (rows 97 131 164 266 336 33 68 152 280), lower := (rows 97 131 164 266 336 33 68 128 256), losses := [] }

theorem u2950 : Upper (D 9) (R 9) [96,129,160,258,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2950 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2951 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 167, targets := 256 },{ cop := 0, region := 404, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 97 131 164 266 336 33 72 148 276), lower := (rows 97 131 164 266 336 33 72 128 256), losses := [] }

theorem u2951 : Upper (D 9) (R 9) [96,129,160,258,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2951 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2952 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 80, targets := 1 }], pairs := [(1,6),(2,6),(3,6),(4,0)], upper := (rows 97 131 164 266 336 33 80 140 268), lower := (rows 97 131 164 266 336 33 80 128 256), losses := [] }

theorem u2952 : Upper (D 9) (R 9) [96,129,160,258,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2952 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2953 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 404, targets := 1 },{ cop := 2, region := 337, targets := 128 }], pairs := [(0,7),(2,0),(4,0),(4,7)], upper := (rows 97 131 164 266 336 40 65 148 276), lower := (rows 97 131 164 266 336 40 65 128 256), losses := [] }

theorem u2953 : Upper (D 9) (R 9) [96,129,160,258,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2953 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2954 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 131 164 266 336 40 68 145 273), lower := (rows 97 131 164 266 336 40 68 128 256), losses := [] }

theorem u2954 : Upper (D 9) (R 9) [96,129,160,258,320,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2954 [(5,3),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2955 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 164 266 336 40 80 133 261), lower := (rows 97 131 164 266 336 40 80 128 256), losses := [] }

theorem u2955 : Upper (D 9) (R 9) [96,129,160,258,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2955 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2956 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 7, region := 99, targets := 256 }], pairs := [(0,8),(2,0),(3,0),(4,0)], upper := (rows 97 131 164 268 336 33 66 152 280), lower := (rows 97 131 164 268 336 33 66 128 256), losses := [] }

theorem u2956 : Upper (D 9) (R 9) [96,129,160,260,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2956 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2957 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 167, targets := 256 },{ cop := 0, region := 402, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8)], upper := (rows 97 131 164 268 336 33 72 146 274), lower := (rows 97 131 164 268 336 33 72 128 256), losses := [] }

theorem u2957 : Upper (D 9) (R 9) [96,129,160,260,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2957 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2958 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 80, targets := 1 }], pairs := [(1,6),(2,6),(3,6),(4,0)], upper := (rows 97 131 164 268 336 33 80 138 266), lower := (rows 97 131 164 268 336 33 80 128 256), losses := [] }

theorem u2958 : Upper (D 9) (R 9) [96,129,160,260,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2958 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2959 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,5),(1,8),(4,5)], upper := (rows 97 131 164 268 336 40 65 146 274), lower := (rows 97 131 164 268 336 40 65 128 256), losses := [] }

theorem u2959 : Upper (D 9) (R 9) [96,129,160,260,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2959 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2960 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,5),(4,5)], upper := (rows 97 131 164 268 336 40 66 145 273), lower := (rows 97 131 164 268 336 40 66 128 256), losses := [] }

theorem u2960 : Upper (D 9) (R 9) [96,129,160,260,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2960 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2961 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 164 268 336 40 80 131 259), lower := (rows 97 131 164 268 336 40 80 128 256), losses := [] }

theorem u2961 : Upper (D 9) (R 9) [96,129,160,260,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2961 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2962 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 134 262 152 304 33 65 200 328), lower := (rows 97 134 262 152 304 33 65 128 256), losses := [] }

theorem u2962 : Upper (D 9) (R 9) [96,132,258,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2962 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2963 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,7)], upper := (rows 97 134 262 152 304 33 72 193 321), lower := (rows 97 134 262 152 304 33 72 128 256), losses := [] }

theorem u2963 : Upper (D 9) (R 9) [96,132,258,144,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2963 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2964 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 1, region := 97, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 134 262 168 336 33 65 152 280), lower := (rows 97 134 262 168 336 33 65 128 256), losses := [] }

theorem u2964 : Upper (D 9) (R 9) [96,132,258,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2964 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2965 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 1, region := 105, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(4,5)], upper := (rows 97 134 262 168 336 33 72 145 273), lower := (rows 97 134 262 168 336 33 72 128 256), losses := [] }

theorem u2965 : Upper (D 9) (R 9) [96,132,258,160,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2965 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2966 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 2, region := 80, targets := 1 }], pairs := [(1,6),(2,6),(3,6),(4,0)], upper := (rows 97 134 262 168 336 33 80 137 265), lower := (rows 97 134 262 168 336 33 80 128 256), losses := [] }

theorem u2966 : Upper (D 9) (R 9) [96,132,258,160,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2966 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2967 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 134 268 152 304 33 65 194 322), lower := (rows 97 134 268 152 304 33 65 128 256), losses := [] }

theorem u2967 : Upper (D 9) (R 9) [96,132,264,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2967 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2968 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 2, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(4,7)], upper := (rows 97 134 268 152 304 33 66 193 321), lower := (rows 97 134 268 152 304 33 66 128 256), losses := [] }

theorem u2968 : Upper (D 9) (R 9) [96,132,264,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2968 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2969 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 134 268 168 336 33 65 146 274), lower := (rows 97 134 268 168 336 33 65 128 256), losses := [] }

theorem u2969 : Upper (D 9) (R 9) [96,132,264,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2969 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2970 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 1, region := 105, targets := 256 }], pairs := [(0,7),(0,8),(3,8),(4,7)], upper := (rows 97 134 268 168 336 33 66 145 273), lower := (rows 97 134 268 168 336 33 66 128 256), losses := [] }

theorem u2970 : Upper (D 9) (R 9) [96,132,264,160,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2970 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2971 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 134 268 168 336 33 80 131 259), lower := (rows 97 134 268 168 336 33 80 128 256), losses := [] }

theorem u2971 : Upper (D 9) (R 9) [96,132,264,160,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2971 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2972 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 8, region := 97, targets := 128 }], pairs := [(0,7),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 134 292 152 336 33 65 138 266), lower := (rows 97 134 292 152 336 33 65 128 256), losses := [] }

theorem u2972 : Upper (D 9) (R 9) [96,132,288,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2972 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2973 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 1, region := 97, targets := 384 }], pairs := [(0,7),(0,8),(3,5),(4,5)], upper := (rows 97 134 292 152 336 33 66 137 265), lower := (rows 97 134 292 152 336 33 66 128 256), losses := [] }

theorem u2973 : Upper (D 9) (R 9) [96,132,288,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2973 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2974 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 97, targets := 384 }], pairs := [(0,7),(0,8),(1,6),(2,6)], upper := (rows 97 134 292 152 336 33 72 131 259), lower := (rows 97 134 292 152 336 33 72 128 256), losses := [] }

theorem u2974 : Upper (D 9) (R 9) [96,132,288,144,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2974 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2975 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(3,5),(4,5)], upper := (rows 97 134 292 152 336 34 72 129 257), lower := (rows 97 134 292 152 336 34 72 128 256), losses := [] }

theorem u2975 : Upper (D 9) (R 9) [96,132,288,144,320,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2975 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2976 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 },{ cop := 1, region := 97, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 134 292 200 280 33 65 146 274), lower := (rows 97 134 292 200 280 33 65 128 256), losses := [] }

theorem u2976 : Upper (D 9) (R 9) [96,132,288,192,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2976 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2977 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 309, targets := 128 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 97 134 292 200 280 33 66 145 273), lower := (rows 97 134 292 200 280 33 66 128 256), losses := [] }

theorem u2977 : Upper (D 9) (R 9) [96,132,288,192,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2977 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2978 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(1,6),(2,6)], upper := (rows 97 134 292 200 280 33 80 131 259), lower := (rows 97 134 292 200 280 33 80 128 256), losses := [] }

theorem u2978 : Upper (D 9) (R 9) [96,132,288,192,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2978 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2979 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(3,5),(4,5)], upper := (rows 97 134 292 200 280 34 80 129 257), lower := (rows 97 134 292 200 280 34 80 128 256), losses := [] }

theorem u2979 : Upper (D 9) (R 9) [96,132,288,192,264,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2979 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2980 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 407, targets := 64 },{ cop := 0, region := 488, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0),(4,6)], upper := (rows 7 11 21 104 176 96 448 384 384), lower := (rows 7 11 21 104 176 96 64 128 256), losses := [] }

theorem u2980 : Upper (D 9) (R 9) [6,9,17,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2980 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2981 : Route 9 := (fun mask => (mask,id))

def c2981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u2981 : Upper (D 9) (R 9) [6,9,17,96,160,256] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,160,256] 13 (by decide) (choices 1) [128,256] r2981 c2981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u191
  · exact u192

def b2982 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 407, targets := 64 },{ cop := 0, region := 488, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0),(4,6)], upper := (rows 7 11 21 104 400 96 480 416 416), lower := (rows 7 11 21 104 400 96 64 128 256), losses := [] }

theorem u2982 : Upper (D 9) (R 9) [6,9,17,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2982 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m2983_32 : Upper (D 9) (R 9) [6,9,17,96,384,128,32] 13 :=
  permutation_upper _ _ _ [6,9,17,96,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u193

def r2983 : Route 9 := (fun mask => (mask,id))

def c2983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u2983 : Upper (D 9) (R 9) [6,9,17,96,384,128] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,384,128] 13 (by decide) (choices 1) [32,256] r2983 c2983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m2983_32
  · exact u194

def b2984 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 37 88 176 96 448 384 384), lower := (rows 7 11 37 88 176 96 64 128 256), losses := [] }

theorem u2984 : Upper (D 9) (R 9) [6,9,33,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2984 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2985 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,7)], upper := (rows 7 11 37 88 176 160 320 448 320), lower := (rows 7 11 37 88 176 160 64 128 256), losses := [] }

theorem u2985 : Upper (D 9) (R 9) [6,9,33,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2985 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2986 : Route 9 := (fun mask => (mask,id))

def c2986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u2986 : Upper (D 9) (R 9) [6,9,33,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,160,256] 13 (by decide) (choices 1) [128,256] r2986 c2986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u195
  · exact u196

def b2987 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 37 88 400 96 480 416 416), lower := (rows 7 11 37 88 400 96 64 128 256), losses := [] }

theorem u2987 : Upper (D 9) (R 9) [6,9,33,80,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2987 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2988 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0),(4,0)], upper := (rows 7 11 37 88 400 160 352 480 352), lower := (rows 7 11 37 88 400 160 64 128 256), losses := [{ target := 6, region := (rows 11 10 12 8 16 176 0 128 256), good := (rows 7 15 37 63 432 160 0 160 256) }] }

theorem u2988 : Upper (D 9) (R 9) [6,9,33,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2988 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2989 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 55, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 11 37 200 112 48 448 384 384), lower := (rows 7 11 37 200 112 48 64 128 256), losses := [] }

theorem u2989 : Upper (D 9) (R 9) [6,9,33,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2989 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2990 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 11 37 200 112 160 336 400 272), lower := (rows 7 11 37 200 112 160 64 128 256), losses := [] }

theorem u2990 : Upper (D 9) (R 9) [6,9,33,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2990 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2991 : Route 9 := (fun mask => (mask,id))

def c2991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u2991 : Upper (D 9) (R 9) [6,9,33,192,96,256] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,96,256] 13 (by decide) (choices 1) [16,128,256] r2991 c2991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u197
  · exact u198
  · exact u199

def b2992 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 459, targets := 32 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,5),(1,5),(3,0),(3,5)], upper := (rows 7 11 37 200 304 48 448 448 448), lower := (rows 7 11 37 200 304 48 64 128 256), losses := [] }

theorem u2992 : Upper (D 9) (R 9) [6,9,33,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2992 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2993 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 37 200 304 96 464 400 400), lower := (rows 7 11 37 200 304 96 64 128 256), losses := [] }

theorem u2993 : Upper (D 9) (R 9) [6,9,33,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2993 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2994 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 7 11 37 200 304 288 208 208 464), lower := (rows 7 11 37 200 304 288 64 128 256), losses := [] }

theorem u2994 : Upper (D 9) (R 9) [6,9,33,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2994 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2995 : Route 9 := (fun mask => (mask,id))

def c2995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u2995 : Upper (D 9) (R 9) [6,9,33,192,320,16] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,320,16] 13 (by decide) (choices 1) [32,128,256] r2995 c2995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u200
  · exact u201
  · exact u202

def b2996 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 320 }], pairs := [(0,6),(0,8),(1,6),(1,8),(2,6)], upper := (rows 7 11 37 200 336 160 368 432 304), lower := (rows 7 11 37 200 336 160 64 128 256), losses := [] }

theorem u2996 : Upper (D 9) (R 9) [6,9,33,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2996 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2997 : Route 9 := (fun mask => (mask,id))

def c2997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2997 : Upper (D 9) (R 9) [6,9,33,192,320,256] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,320,256] 13 (by decide) (choices 1) [16,32,128] r2997 c2997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u203
  · exact u204
  · exact u205

def b2998 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 407, targets := 64 },{ cop := 4, region := 356, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(2,6),(4,6)], upper := (rows 7 11 52 104 145 96 448 384 384), lower := (rows 7 11 52 104 145 96 64 128 256), losses := [] }

theorem u2998 : Upper (D 9) (R 9) [6,9,48,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2998 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2999 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 364, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,0),(3,7)], upper := (rows 7 11 52 104 145 160 320 448 320), lower := (rows 7 11 52 104 145 160 64 128 256), losses := [] }

theorem u2999 : Upper (D 9) (R 9) [6,9,48,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2999 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2999
end Delivery.IrregularNine14.P09
