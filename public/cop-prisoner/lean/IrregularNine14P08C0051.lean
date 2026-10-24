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

def b3060 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 392 112 160 113 177 305), lower := (rows 67 38 13 392 112 160 64 128 256), losses := [] }

theorem u3060 : Upper (D 8) (R 8) [66,36,9,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3061 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 392 176 33 112 240 368), lower := (rows 67 38 13 392 176 33 64 128 256), losses := [] }

theorem u3061 : Upper (D 8) (R 8) [66,36,9,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3062 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 13 392 176 48 97 225 353), lower := (rows 67 38 13 392 176 48 64 128 256), losses := [] }

theorem u3062 : Upper (D 8) (R 8) [66,36,9,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3062 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3063 : PairBound 9 := { available := 49, camps := [], pairs := [(1,0)], upper := (rows 67 38 13 392 176 96 113 177 305), lower := (rows 67 38 13 392 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 46 392 176 96 96 128 256) }] }

theorem u3063 : Upper (D 8) (R 8) [66,36,9,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3064 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 392 208 33 112 176 304), lower := (rows 67 38 13 392 208 33 64 128 256), losses := [] }

theorem u3064 : Upper (D 8) (R 8) [66,36,9,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3065 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 13 392 208 48 97 161 289), lower := (rows 67 38 13 392 208 48 64 128 256), losses := [] }

theorem u3065 : Upper (D 8) (R 8) [66,36,9,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3065 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3066 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 28 41 400 33 224 224 480), lower := (rows 67 38 28 41 400 33 64 128 256), losses := [] }

theorem u3066 : Upper (D 8) (R 8) [66,36,24,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3067 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 28 41 400 96 225 161 417), lower := (rows 67 38 28 41 400 96 64 128 256), losses := [] }

theorem u3067 : Upper (D 8) (R 8) [66,36,24,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3068 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 41 400 160 97 225 353), lower := (rows 67 38 28 41 400 160 64 128 256), losses := [] }

theorem u3068 : Upper (D 8) (R 8) [66,36,24,33,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3069 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 28 137 304 33 224 224 480), lower := (rows 67 38 28 137 304 33 64 128 256), losses := [] }

theorem u3069 : Upper (D 8) (R 8) [66,36,24,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3070 : Route 9 := (fun mask => (mask,id))

def c3070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3070 : Upper (D 8) (R 8) [66,36,24,129,288,64] 13 := by
  apply FastRouting.sound _ _ [66,36,24,129,288,64] 13 (by decide) (choices 1) [1,32,128] r3070 c3070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u399
  · exact u400
  · exact u401

def b3071 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 137 304 160 97 225 353), lower := (rows 67 38 28 137 304 160 64 128 256), losses := [] }

theorem u3071 : Upper (D 8) (R 8) [66,36,24,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3072 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 28 168 273 33 224 224 480), lower := (rows 67 38 28 168 273 33 64 128 256), losses := [] }

theorem u3072 : Upper (D 8) (R 8) [66,36,24,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3073 : Route 9 := (fun mask => (mask,id))

def c3073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3073 : Upper (D 8) (R 8) [66,36,24,160,257,64] 13 := by
  apply FastRouting.sound _ _ [66,36,24,160,257,64] 13 (by decide) (choices 1) [1,32,128] r3073 c3073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u402
  · exact u403
  · exact u404

def b3074 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 28 168 273 160 97 225 353), lower := (rows 67 38 28 168 273 160 64 128 256), losses := [] }

theorem u3074 : Upper (D 8) (R 8) [66,36,24,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3075 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 56 208 33 360 424 296), lower := (rows 67 38 133 56 208 33 64 128 256), losses := [] }

theorem u3075 : Upper (D 8) (R 8) [66,36,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3076 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 38 133 56 208 40 353 417 289), lower := (rows 67 38 133 56 208 40 64 128 256), losses := [] }

theorem u3076 : Upper (D 8) (R 8) [66,36,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3076 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3077 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 38 133 56 208 288 105 169 297), lower := (rows 67 38 133 56 208 288 64 128 256), losses := [] }

theorem u3077 : Upper (D 8) (R 8) [66,36,129,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3077 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3078 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 56 280 33 224 224 480), lower := (rows 67 38 133 56 280 33 64 128 256), losses := [] }

theorem u3078 : Upper (D 8) (R 8) [66,36,129,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3079 : PairBound 9 := { available := 161, camps := [], pairs := [(1,0)], upper := (rows 67 38 133 56 280 96 225 161 417), lower := (rows 67 38 133 56 280 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 166 56 280 96 96 128 256) }] }

theorem u3079 : Upper (D 8) (R 8) [66,36,129,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3080 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 133 56 280 160 97 225 353), lower := (rows 67 38 133 56 280 160 64 128 256), losses := [] }

theorem u3080 : Upper (D 8) (R 8) [66,36,129,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3081 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 56 336 33 232 168 424), lower := (rows 67 38 133 56 336 33 64 128 256), losses := [] }

theorem u3081 : Upper (D 8) (R 8) [66,36,129,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3082 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 133 56 336 40 225 161 417), lower := (rows 67 38 133 56 336 40 64 128 256), losses := [] }

theorem u3082 : Upper (D 8) (R 8) [66,36,129,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3082 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3083 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 133 56 336 160 105 169 297), lower := (rows 67 38 133 56 336 160 64 128 256), losses := [] }

theorem u3083 : Upper (D 8) (R 8) [66,36,129,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3084 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 56 400 33 104 232 360), lower := (rows 67 38 133 56 400 33 64 128 256), losses := [] }

theorem u3084 : Upper (D 8) (R 8) [66,36,129,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3085 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 133 56 400 40 97 225 353), lower := (rows 67 38 133 56 400 40 64 128 256), losses := [] }

theorem u3085 : Upper (D 8) (R 8) [66,36,129,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3085 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3086 : PairBound 9 := { available := 41, camps := [], pairs := [(1,0)], upper := (rows 67 38 133 56 400 96 105 169 297), lower := (rows 67 38 133 56 400 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 166 56 400 96 96 128 256) }] }

theorem u3086 : Upper (D 8) (R 8) [66,36,129,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3087 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 88 176 33 360 424 296), lower := (rows 67 38 133 88 176 33 64 128 256), losses := [] }

theorem u3087 : Upper (D 8) (R 8) [66,36,129,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3088 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 38 133 88 176 40 353 417 289), lower := (rows 67 38 133 88 176 40 64 128 256), losses := [] }

theorem u3088 : Upper (D 8) (R 8) [66,36,129,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3088 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3089 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 38 133 88 176 288 105 169 297), lower := (rows 67 38 133 88 176 288 64 128 256), losses := [] }

theorem u3089 : Upper (D 8) (R 8) [66,36,129,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3089 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3090 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 88 304 33 232 168 424), lower := (rows 67 38 133 88 304 33 64 128 256), losses := [] }

theorem u3090 : Upper (D 8) (R 8) [66,36,129,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3091 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 133 88 304 40 225 161 417), lower := (rows 67 38 133 88 304 40 64 128 256), losses := [] }

theorem u3091 : Upper (D 8) (R 8) [66,36,129,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3091 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3092 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 133 88 304 160 105 169 297), lower := (rows 67 38 133 88 304 160 64 128 256), losses := [] }

theorem u3092 : Upper (D 8) (R 8) [66,36,129,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3093 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 88 400 33 104 168 296), lower := (rows 67 38 133 88 400 33 64 128 256), losses := [] }

theorem u3093 : Upper (D 8) (R 8) [66,36,129,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3094 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 133 88 400 40 97 161 289), lower := (rows 67 38 133 88 400 40 64 128 256), losses := [] }

theorem u3094 : Upper (D 8) (R 8) [66,36,129,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3094 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3095 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 104 152 33 368 432 304), lower := (rows 67 38 133 104 152 33 64 128 256), losses := [] }

theorem u3095 : Upper (D 8) (R 8) [66,36,129,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3096 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 38 133 104 152 48 353 417 289), lower := (rows 67 38 133 104 152 48 64 128 256), losses := [] }

theorem u3096 : Upper (D 8) (R 8) [66,36,129,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3096 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3097 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 38 133 104 152 288 113 177 305), lower := (rows 67 38 133 104 152 288 64 128 256), losses := [] }

theorem u3097 : Upper (D 8) (R 8) [66,36,129,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3097 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3098 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 104 176 33 344 408 280), lower := (rows 67 38 133 104 176 33 64 128 256), losses := [] }

theorem u3098 : Upper (D 8) (R 8) [66,36,129,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3099 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 67 38 133 104 176 40 337 401 273), lower := (rows 67 38 133 104 176 40 64 128 256), losses := [] }

theorem u3099 : Upper (D 8) (R 8) [66,36,129,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3099 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3100 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 67 38 133 104 176 48 329 393 265), lower := (rows 67 38 133 104 176 48 64 128 256), losses := [] }

theorem u3100 : Upper (D 8) (R 8) [66,36,129,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3100 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3101 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 38 133 104 176 288 89 153 281), lower := (rows 67 38 133 104 176 288 64 128 256), losses := [] }

theorem u3101 : Upper (D 8) (R 8) [66,36,129,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3101 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3102 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 104 280 33 240 176 432), lower := (rows 67 38 133 104 280 33 64 128 256), losses := [] }

theorem u3102 : Upper (D 8) (R 8) [66,36,129,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3103 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 133 104 280 48 225 161 417), lower := (rows 67 38 133 104 280 48 64 128 256), losses := [] }

theorem u3103 : Upper (D 8) (R 8) [66,36,129,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3103 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3104 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 133 104 280 160 113 177 305), lower := (rows 67 38 133 104 280 160 64 128 256), losses := [] }

theorem u3104 : Upper (D 8) (R 8) [66,36,129,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3105 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 104 304 33 216 152 408), lower := (rows 67 38 133 104 304 33 64 128 256), losses := [] }

theorem u3105 : Upper (D 8) (R 8) [66,36,129,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3106 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 38 133 104 304 40 209 145 401), lower := (rows 67 38 133 104 304 40 64 128 256), losses := [] }

theorem u3106 : Upper (D 8) (R 8) [66,36,129,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3106 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3107 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 38 133 104 304 48 201 137 393), lower := (rows 67 38 133 104 304 48 64 128 256), losses := [] }

theorem u3107 : Upper (D 8) (R 8) [66,36,129,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3107 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3108 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 133 104 304 160 89 153 281), lower := (rows 67 38 133 104 304 160 64 128 256), losses := [] }

theorem u3108 : Upper (D 8) (R 8) [66,36,129,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3109 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 104 400 33 120 184 312), lower := (rows 67 38 133 104 400 33 64 128 256), losses := [] }

theorem u3109 : Upper (D 8) (R 8) [66,36,129,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3110 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 38 133 104 400 40 113 177 305), lower := (rows 67 38 133 104 400 40 64 128 256), losses := [] }

theorem u3110 : Upper (D 8) (R 8) [66,36,129,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3110 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3111 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 38 133 104 400 48 105 169 297), lower := (rows 67 38 133 104 400 48 64 128 256), losses := [] }

theorem u3111 : Upper (D 8) (R 8) [66,36,129,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3111 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3112 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 152 304 33 104 232 360), lower := (rows 67 38 133 152 304 33 64 128 256), losses := [] }

theorem u3112 : Upper (D 8) (R 8) [66,36,129,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3113 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 133 152 304 40 97 225 353), lower := (rows 67 38 133 152 304 40 64 128 256), losses := [] }

theorem u3113 : Upper (D 8) (R 8) [66,36,129,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3113 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3114 : PairBound 9 := { available := 41, camps := [], pairs := [(1,0)], upper := (rows 67 38 133 152 304 96 105 169 297), lower := (rows 67 38 133 152 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 97 64 128 256), good := (rows 98 38 166 152 304 96 96 128 256) }] }

theorem u3114 : Upper (D 8) (R 8) [66,36,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3115 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 152 336 33 104 168 296), lower := (rows 67 38 133 152 336 33 64 128 256), losses := [] }

theorem u3115 : Upper (D 8) (R 8) [66,36,129,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3116 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 133 152 336 40 97 161 289), lower := (rows 67 38 133 152 336 40 64 128 256), losses := [] }

theorem u3116 : Upper (D 8) (R 8) [66,36,129,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3116 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3117 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 168 280 33 112 240 368), lower := (rows 67 38 133 168 280 33 64 128 256), losses := [] }

theorem u3117 : Upper (D 8) (R 8) [66,36,129,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3118 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 133 168 280 48 97 225 353), lower := (rows 67 38 133 168 280 48 64 128 256), losses := [] }

theorem u3118 : Upper (D 8) (R 8) [66,36,129,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3118 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3119 : PairBound 9 := { available := 49, camps := [], pairs := [(1,0)], upper := (rows 67 38 133 168 280 96 113 177 305), lower := (rows 67 38 133 168 280 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 97 64 128 256), good := (rows 98 46 174 168 280 96 96 128 256) }] }

theorem u3119 : Upper (D 8) (R 8) [66,36,129,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3119
end Delivery.IrregularNine14.P08
