import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0003

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3060 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(2,1),(4,0),(4,5)], upper := (rows 7 290 76 41 82 160 192 145 273), lower := (rows 7 290 76 41 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 224 224 128 256), good := (rows 22 370 108 108 114 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 16 224 224 128 256), good := (rows 5 352 108 109 112 224 224 224 256) }] }

theorem u3060 : Upper (D 7) (R 7) [6,288,72,33,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3061 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 76 41 146 160 65 208 336), lower := (rows 7 290 76 41 146 160 65 128 256), losses := [] }

theorem u3061 : Upper (D 7) (R 7) [6,288,72,33,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3062 : Route 9 := (fun mask => (mask,id))

def c3062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3062 : Upper (D 7) (R 7) [6,288,72,33,130,128,16] 13 := by
  apply FastRouting.sound _ _ [6,288,72,33,130,128,16] 13 (by decide) (choices 1) [1,64] r3062 c3062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u185
  · exact u186

def b3063 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 76 41 208 160 65 146 274), lower := (rows 7 290 76 41 208 160 65 128 256), losses := [] }

theorem u3063 : Upper (D 7) (R 7) [6,288,72,33,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3064 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(2,7),(3,7),(4,5)], upper := (rows 7 290 76 41 208 160 66 145 273), lower := (rows 7 290 76 41 208 160 66 128 256), losses := [] }

theorem u3064 : Upper (D 7) (R 7) [6,288,72,33,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3065 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 76 41 208 160 80 131 259), lower := (rows 7 290 76 41 208 160 80 128 256), losses := [] }

theorem u3065 : Upper (D 7) (R 7) [6,288,72,33,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3065 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3066 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 76 56 82 160 65 129 385), lower := (rows 7 290 76 56 82 160 65 128 256), losses := [] }

theorem u3066 : Upper (D 7) (R 7) [6,288,72,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3067 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(1,6),(2,0),(4,5)], upper := (rows 7 290 76 56 82 160 192 129 257), lower := (rows 7 290 76 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 30 26 18 224 224 128 256), good := (rows 30 382 108 124 126 224 224 224 256) }] }

theorem u3067 : Upper (D 7) (R 7) [6,288,72,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3068 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 108, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 7 290 76 56 145 96 65 130 386), lower := (rows 7 290 76 56 145 96 65 128 256), losses := [] }

theorem u3068 : Upper (D 7) (R 7) [6,288,72,48,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3069 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 8, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,6)], upper := (rows 7 290 76 56 145 96 66 129 385), lower := (rows 7 290 76 56 145 96 66 128 256), losses := [] }

theorem u3069 : Upper (D 7) (R 7) [6,288,72,48,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3070 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 290 76 56 145 96 192 131 259), lower := (rows 7 290 76 56 145 96 192 128 256), losses := [] }

theorem u3070 : Upper (D 7) (R 7) [6,288,72,48,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3071 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(2,7),(3,7),(4,5)], upper := (rows 7 290 76 56 146 33 65 192 448), lower := (rows 7 290 76 56 146 33 65 128 256), losses := [] }

theorem u3071 : Upper (D 7) (R 7) [6,288,72,48,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3072 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(2,0),(4,5)], upper := (rows 7 290 76 56 146 33 192 193 321), lower := (rows 7 290 76 56 146 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 208 128 256), good := (rows 6 290 76 124 210 32 192 192 256) }] }

theorem u3072 : Upper (D 7) (R 7) [6,288,72,48,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3073 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,7),(2,7),(3,7),(4,5)], upper := (rows 7 290 76 56 146 96 65 129 385), lower := (rows 7 290 76 56 146 96 65 128 256), losses := [] }

theorem u3073 : Upper (D 7) (R 7) [6,288,72,48,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3074 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 290 76 56 146 96 192 129 257), lower := (rows 7 290 76 56 146 96 192 128 256), losses := [] }

theorem u3074 : Upper (D 7) (R 7) [6,288,72,48,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3075 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 },{ cop := 3, region := 386, targets := 1 }], pairs := [(0,6),(1,0),(1,6),(4,5)], upper := (rows 7 290 76 56 208 33 65 130 386), lower := (rows 7 290 76 56 208 33 65 128 256), losses := [] }

theorem u3075 : Upper (D 7) (R 7) [6,288,72,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3076 : Route 9 := (fun mask => (mask,id))

def c3076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3076 : Upper (D 7) (R 7) [6,288,72,48,192,1,2] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48,192,1,2] 13 (by decide) (choices 1) [1] r3076 c3076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u187

def b3077 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 76 56 208 33 192 131 259), lower := (rows 7 290 76 56 208 33 192 128 256), losses := [] }

theorem u3077 : Upper (D 7) (R 7) [6,288,72,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3078 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 4, region := 172, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 290 76 137 81 160 66 176 304), lower := (rows 7 290 76 137 81 160 66 128 256), losses := [] }

theorem u3078 : Upper (D 7) (R 7) [6,288,72,129,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3079 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5)], upper := (rows 7 290 76 137 81 160 80 162 290), lower := (rows 7 290 76 137 81 160 80 128 256), losses := [] }

theorem u3079 : Upper (D 7) (R 7) [6,288,72,129,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3079 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3080 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 116, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 290 76 137 81 160 96 146 274), lower := (rows 7 290 76 137 81 160 96 128 256), losses := [] }

theorem u3080 : Upper (D 7) (R 7) [6,288,72,129,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3081 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 76 137 82 33 80 160 416), lower := (rows 7 290 76 137 82 33 80 128 256), losses := [] }

theorem u3081 : Upper (D 7) (R 7) [6,288,72,129,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3081 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3082 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 3, region := 100, targets := 2 }], pairs := [(0,5),(2,1),(2,5),(3,5)], upper := (rows 7 290 76 137 82 33 96 144 400), lower := (rows 7 290 76 137 82 33 96 128 256), losses := [] }

theorem u3082 : Upper (D 7) (R 7) [6,288,72,129,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3083 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 290 76 137 82 33 192 176 304), lower := (rows 7 290 76 137 82 33 192 128 256), losses := [] }

theorem u3083 : Upper (D 7) (R 7) [6,288,72,129,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3084 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 7 290 76 137 82 48 65 160 416), lower := (rows 7 290 76 137 82 48 65 128 256), losses := [] }

theorem u3084 : Upper (D 7) (R 7) [6,288,72,129,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3084 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3085 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 290 76 137 82 48 96 129 385), lower := (rows 7 290 76 137 82 48 96 128 256), losses := [] }

theorem u3085 : Upper (D 7) (R 7) [6,288,72,129,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3085 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3086 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 290 76 137 82 48 192 161 289), lower := (rows 7 290 76 137 82 48 192 128 256), losses := [] }

theorem u3086 : Upper (D 7) (R 7) [6,288,72,129,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3086 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3087 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 2, region := 434, targets := 1 }], pairs := [(1,0),(4,0),(4,5),(4,7)], upper := (rows 7 290 76 137 82 160 65 176 304), lower := (rows 7 290 76 137 82 160 65 128 256), losses := [] }

theorem u3087 : Upper (D 7) (R 7) [6,288,72,129,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3088 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 290 76 137 82 160 80 161 289), lower := (rows 7 290 76 137 82 160 80 128 256), losses := [] }

theorem u3088 : Upper (D 7) (R 7) [6,288,72,129,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3088 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3089 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 290 76 137 82 160 96 145 273), lower := (rows 7 290 76 137 82 160 96 128 256), losses := [] }

theorem u3089 : Upper (D 7) (R 7) [6,288,72,129,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3090 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 8, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 7 290 76 137 112 34 65 144 400), lower := (rows 7 290 76 137 112 34 65 128 256), losses := [] }

theorem u3090 : Upper (D 7) (R 7) [6,288,72,129,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3091 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 290 76 137 112 34 80 129 385), lower := (rows 7 290 76 137 112 34 80 128 256), losses := [] }

theorem u3091 : Upper (D 7) (R 7) [6,288,72,129,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3091 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3092 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 290 76 137 112 34 192 145 273), lower := (rows 7 290 76 137 112 34 192 128 256), losses := [] }

theorem u3092 : Upper (D 7) (R 7) [6,288,72,129,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3093 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 3, region := 116, targets := 2 }], pairs := [(1,0),(2,1),(4,0),(4,1)], upper := (rows 7 290 76 137 112 160 65 146 274), lower := (rows 7 290 76 137 112 160 65 128 256), losses := [] }

theorem u3093 : Upper (D 7) (R 7) [6,288,72,129,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3094 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 129 }], pairs := [(2,0),(3,1),(4,0),(4,7)], upper := (rows 7 290 76 137 112 160 66 145 273), lower := (rows 7 290 76 137 112 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 30 168 67 128 256), good := (rows 86 370 124 252 112 160 82 160 256) },{ target := 1, region := (rows 1 0 4 9 20 169 64 129 257), good := (rows 445 288 124 425 112 160 64 160 256) }] }

theorem u3094 : Upper (D 7) (R 7) [6,288,72,129,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3095 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 290 76 137 112 160 80 131 259), lower := (rows 7 290 76 137 112 160 80 128 256), losses := [] }

theorem u3095 : Upper (D 7) (R 7) [6,288,72,129,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3095 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3096 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 76 137 146 33 80 224 352), lower := (rows 7 290 76 137 146 33 80 128 256), losses := [] }

theorem u3096 : Upper (D 7) (R 7) [6,288,72,129,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3096 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3097 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 100, targets := 130 },{ cop := 5, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,7),(4,0)], upper := (rows 7 290 76 137 146 33 96 208 336), lower := (rows 7 290 76 137 146 33 96 128 256), losses := [] }

theorem u3097 : Upper (D 7) (R 7) [6,288,72,129,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3098 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 7 290 76 137 146 48 65 224 352), lower := (rows 7 290 76 137 146 48 65 128 256), losses := [] }

theorem u3098 : Upper (D 7) (R 7) [6,288,72,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3098 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3099 : Route 9 := (fun mask => (mask,id))

def c3099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3099 : Upper (D 7) (R 7) [6,288,72,129,130,16,32] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129,130,16,32] 13 (by decide) (choices 1) [1,64] r3099 c3099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u188
  · exact u189

def b3100 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 290 76 137 146 96 65 176 304), lower := (rows 7 290 76 137 146 96 65 128 256), losses := [] }

theorem u3100 : Upper (D 7) (R 7) [6,288,72,129,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3101 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 76 137 146 96 80 161 289), lower := (rows 7 290 76 137 146 96 80 128 256), losses := [] }

theorem u3101 : Upper (D 7) (R 7) [6,288,72,129,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3101 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3102 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 290 76 137 146 96 96 145 273), lower := (rows 7 290 76 137 146 96 96 128 256), losses := [] }

theorem u3102 : Upper (D 7) (R 7) [6,288,72,129,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3103 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 290 76 137 176 96 65 146 274), lower := (rows 7 290 76 137 176 96 65 128 256), losses := [] }

theorem u3103 : Upper (D 7) (R 7) [6,288,72,129,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3104 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 7 290 76 137 176 96 66 145 273), lower := (rows 7 290 76 137 176 96 66 128 256), losses := [{ target := 0, region := (rows 0 258 12 8 24 367 323 128 256), good := (rows 102 354 124 252 176 96 98 128 354) }] }

theorem u3104 : Upper (D 7) (R 7) [6,288,72,129,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3105 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 290 76 137 176 96 80 131 259), lower := (rows 7 290 76 137 176 96 80 128 256), losses := [] }

theorem u3105 : Upper (D 7) (R 7) [6,288,72,129,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3105 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3106 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 466, targets := 1 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 290 76 137 208 33 66 176 304), lower := (rows 7 290 76 137 208 33 66 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 123 32 99 162 290), good := (rows 470 498 92 220 208 498 466 128 256) },{ target := 1, region := (rows 1 0 4 41 20 41 64 133 261), good := (rows 445 296 508 425 208 425 64 128 256) }] }

theorem u3106 : Upper (D 7) (R 7) [6,288,72,129,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3107 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 7 290 76 137 208 33 80 162 290), lower := (rows 7 290 76 137 208 33 80 128 256), losses := [] }

theorem u3107 : Upper (D 7) (R 7) [6,288,72,129,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3107 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3108 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 116, targets := 2 },{ cop := 5, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(4,0),(4,1)], upper := (rows 7 290 76 137 208 33 96 146 274), lower := (rows 7 290 76 137 208 33 96 128 256), losses := [] }

theorem u3108 : Upper (D 7) (R 7) [6,288,72,129,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3109 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 84, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 76 137 208 34 65 176 304), lower := (rows 7 290 76 137 208 34 65 128 256), losses := [] }

theorem u3109 : Upper (D 7) (R 7) [6,288,72,129,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3110 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 290 76 137 208 34 80 161 289), lower := (rows 7 290 76 137 208 34 80 128 256), losses := [] }

theorem u3110 : Upper (D 7) (R 7) [6,288,72,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3110 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3111 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 129 },{ cop := 8, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 7 290 76 137 208 34 96 145 273), lower := (rows 7 290 76 137 208 34 96 128 256), losses := [{ target := 0, region := (rows 0 258 12 8 24 291 363 128 256), good := (rows 102 354 92 252 208 98 96 128 354) }] }

theorem u3111 : Upper (D 7) (R 7) [6,288,72,129,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3112 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 3, region := 68, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 290 76 137 208 48 65 162 290), lower := (rows 7 290 76 137 208 48 65 128 256), losses := [] }

theorem u3112 : Upper (D 7) (R 7) [6,288,72,129,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3112 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3113 : PairBound 9 := { available := 33, camps := [], pairs := [(2,0),(3,1),(4,0)], upper := (rows 7 290 76 137 208 48 66 161 289), lower := (rows 7 290 76 137 208 48 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 67 128 256), good := (rows 102 354 124 252 240 48 66 128 256) },{ target := 1, region := (rows 1 0 4 9 20 53 64 137 265), good := (rows 445 288 508 425 240 48 64 128 256) }] }

theorem u3113 : Upper (D 7) (R 7) [6,288,72,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3113 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3114 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 290 76 137 208 48 96 131 259), lower := (rows 7 290 76 137 208 48 96 128 256), losses := [] }

theorem u3114 : Upper (D 7) (R 7) [6,288,72,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3114 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3115 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 138 49 160 65 208 336), lower := (rows 7 290 76 138 49 160 65 128 256), losses := [] }

theorem u3115 : Upper (D 7) (R 7) [6,288,72,130,33,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3116 : Route 9 := (fun mask => (mask,id))

def c3116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3116 : Upper (D 7) (R 7) [6,288,72,130,33,128,16] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,33,128,16] 13 (by decide) (choices 1) [1,64] r3116 c3116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u190
  · exact u191

def b3117 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 138 81 160 65 176 304), lower := (rows 7 290 76 138 81 160 65 128 256), losses := [] }

theorem u3117 : Upper (D 7) (R 7) [6,288,72,130,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3118 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 76 138 81 160 80 161 289), lower := (rows 7 290 76 138 81 160 80 128 256), losses := [] }

theorem u3118 : Upper (D 7) (R 7) [6,288,72,130,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3118 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3119 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(3,6)], upper := (rows 7 290 76 138 81 160 96 145 273), lower := (rows 7 290 76 138 81 160 96 128 256), losses := [] }

theorem u3119 : Upper (D 7) (R 7) [6,288,72,130,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3119
end Delivery.IrregularNine14.P07
