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

def b3120 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 168 304 33 88 216 344), lower := (rows 67 38 133 168 304 33 64 128 256), losses := [] }

theorem u3120 : Upper (D 8) (R 8) [66,36,129,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3121 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 38 133 168 304 40 81 209 337), lower := (rows 67 38 133 168 304 40 64 128 256), losses := [] }

theorem u3121 : Upper (D 8) (R 8) [66,36,129,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3121 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3122 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 67 38 133 168 304 48 73 201 329), lower := (rows 67 38 133 168 304 48 64 128 256), losses := [] }

theorem u3122 : Upper (D 8) (R 8) [66,36,129,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3122 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3123 : PairBound 9 := { available := 25, camps := [], pairs := [(1,0)], upper := (rows 67 38 133 168 304 96 89 153 281), lower := (rows 67 38 133 168 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 97 64 128 256), good := (rows 98 46 174 168 304 96 96 128 256) }] }

theorem u3123 : Upper (D 8) (R 8) [66,36,129,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3124 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 168 336 33 120 184 312), lower := (rows 67 38 133 168 336 33 64 128 256), losses := [] }

theorem u3124 : Upper (D 8) (R 8) [66,36,129,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3125 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 38 133 168 336 40 113 177 305), lower := (rows 67 38 133 168 336 40 64 128 256), losses := [] }

theorem u3125 : Upper (D 8) (R 8) [66,36,129,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3125 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3126 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 38 133 168 336 48 105 169 297), lower := (rows 67 38 133 168 336 48 64 128 256), losses := [] }

theorem u3126 : Upper (D 8) (R 8) [66,36,129,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3126 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3127 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 200 280 33 112 176 304), lower := (rows 67 38 133 200 280 33 64 128 256), losses := [] }

theorem u3127 : Upper (D 8) (R 8) [66,36,129,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3128 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 133 200 280 48 97 161 289), lower := (rows 67 38 133 200 280 48 64 128 256), losses := [] }

theorem u3128 : Upper (D 8) (R 8) [66,36,129,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3128 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3129 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 200 304 33 120 184 312), lower := (rows 67 38 133 200 304 33 64 128 256), losses := [] }

theorem u3129 : Upper (D 8) (R 8) [66,36,129,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3130 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 38 133 200 304 40 113 177 305), lower := (rows 67 38 133 200 304 40 64 128 256), losses := [] }

theorem u3130 : Upper (D 8) (R 8) [66,36,129,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3130 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3131 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 38 133 200 304 48 105 169 297), lower := (rows 67 38 133 200 304 48 64 128 256), losses := [] }

theorem u3131 : Upper (D 8) (R 8) [66,36,129,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3131 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3132 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 140 25 304 33 224 224 480), lower := (rows 67 38 140 25 304 33 64 128 256), losses := [] }

theorem u3132 : Upper (D 8) (R 8) [66,36,136,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3133 : Route 9 := (fun mask => (mask,id))

def c3133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3133 : Upper (D 8) (R 8) [66,36,136,17,288,64] 13 := by
  apply FastRouting.sound _ _ [66,36,136,17,288,64] 13 (by decide) (choices 1) [1,32,128] r3133 c3133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u405
  · exact u406
  · exact u407

def b3134 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 25 304 160 97 225 353), lower := (rows 67 38 140 25 304 160 64 128 256), losses := [] }

theorem u3134 : Upper (D 8) (R 8) [66,36,136,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3135 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 41 112 33 464 400 400), lower := (rows 67 38 140 41 112 33 64 128 256), losses := [] }

theorem u3135 : Upper (D 8) (R 8) [66,36,136,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3136 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 67 38 140 41 112 48 449 385 385), lower := (rows 67 38 140 41 112 48 64 128 256), losses := [] }

theorem u3136 : Upper (D 8) (R 8) [66,36,136,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3136 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3137 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 41 112 160 337 401 273), lower := (rows 67 38 140 41 112 160 64 128 256), losses := [] }

theorem u3137 : Upper (D 8) (R 8) [66,36,136,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3138 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 38 140 41 112 288 209 145 401), lower := (rows 67 38 140 41 112 288 64 128 256), losses := [] }

theorem u3138 : Upper (D 8) (R 8) [66,36,136,33,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3138 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3139 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 41 176 33 336 464 336), lower := (rows 67 38 140 41 176 33 64 128 256), losses := [] }

theorem u3139 : Upper (D 8) (R 8) [66,36,136,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3140 : PairBound 9 := { available := 321, camps := [], pairs := [], upper := (rows 67 38 140 41 176 48 321 449 321), lower := (rows 67 38 140 41 176 48 64 128 256), losses := [] }

theorem u3140 : Upper (D 8) (R 8) [66,36,136,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3140 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3141 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 41 176 96 337 401 273), lower := (rows 67 38 140 41 176 96 64 128 256), losses := [] }

theorem u3141 : Upper (D 8) (R 8) [66,36,136,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3142 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 38 140 41 176 288 81 209 337), lower := (rows 67 38 140 41 176 288 64 128 256), losses := [] }

theorem u3142 : Upper (D 8) (R 8) [66,36,136,33,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3142 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3143 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 41 208 33 368 432 304), lower := (rows 67 38 140 41 208 33 64 128 256), losses := [] }

theorem u3143 : Upper (D 8) (R 8) [66,36,136,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3144 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 38 140 41 208 48 353 417 289), lower := (rows 67 38 140 41 208 48 64 128 256), losses := [] }

theorem u3144 : Upper (D 8) (R 8) [66,36,136,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3144 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3145 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 38 140 41 208 288 113 177 305), lower := (rows 67 38 140 41 208 288 64 128 256), losses := [] }

theorem u3145 : Upper (D 8) (R 8) [66,36,136,33,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3145 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3146 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 67 38 140 41 273 48 224 224 480), lower := (rows 67 38 140 41 273 48 64 128 256), losses := [] }

theorem u3146 : Upper (D 8) (R 8) [66,36,136,33,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3146 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3147 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 41 273 96 240 176 432), lower := (rows 67 38 140 41 273 96 64 128 256), losses := [] }

theorem u3147 : Upper (D 8) (R 8) [66,36,136,33,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3148 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 41 273 160 112 240 368), lower := (rows 67 38 140 41 273 160 64 128 256), losses := [] }

theorem u3148 : Upper (D 8) (R 8) [66,36,136,33,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3149 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 41 304 33 208 208 464), lower := (rows 67 38 140 41 304 33 64 128 256), losses := [] }

theorem u3149 : Upper (D 8) (R 8) [66,36,136,33,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3150 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 38 140 41 304 48 193 193 449), lower := (rows 67 38 140 41 304 48 64 128 256), losses := [] }

theorem u3150 : Upper (D 8) (R 8) [66,36,136,33,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3150 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3151 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 41 304 96 209 145 401), lower := (rows 67 38 140 41 304 96 64 128 256), losses := [] }

theorem u3151 : Upper (D 8) (R 8) [66,36,136,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3152 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 41 304 160 81 209 337), lower := (rows 67 38 140 41 304 160 64 128 256), losses := [] }

theorem u3152 : Upper (D 8) (R 8) [66,36,136,33,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3153 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 41 336 33 240 176 432), lower := (rows 67 38 140 41 336 33 64 128 256), losses := [] }

theorem u3153 : Upper (D 8) (R 8) [66,36,136,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3154 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 140 41 336 48 225 161 417), lower := (rows 67 38 140 41 336 48 64 128 256), losses := [] }

theorem u3154 : Upper (D 8) (R 8) [66,36,136,33,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3154 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3155 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 41 336 160 113 177 305), lower := (rows 67 38 140 41 336 160 64 128 256), losses := [] }

theorem u3155 : Upper (D 8) (R 8) [66,36,136,33,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3156 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 41 400 33 112 240 368), lower := (rows 67 38 140 41 400 33 64 128 256), losses := [] }

theorem u3156 : Upper (D 8) (R 8) [66,36,136,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3157 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 140 41 400 48 97 225 353), lower := (rows 67 38 140 41 400 48 64 128 256), losses := [] }

theorem u3157 : Upper (D 8) (R 8) [66,36,136,33,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3157 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3158 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 41 400 96 113 177 305), lower := (rows 67 38 140 41 400 96 64 128 256), losses := [] }

theorem u3158 : Upper (D 8) (R 8) [66,36,136,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3159 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 56 273 33 224 224 480), lower := (rows 67 38 140 56 273 33 64 128 256), losses := [] }

theorem u3159 : Upper (D 8) (R 8) [66,36,136,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3160 : PairBound 9 := { available := 161, camps := [], pairs := [(3,0)], upper := (rows 67 38 140 56 273 96 225 161 417), lower := (rows 67 38 140 56 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 97 64 128 256), good := (rows 98 38 140 56 312 96 96 128 256) }] }

theorem u3160 : Upper (D 8) (R 8) [66,36,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3161 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 56 273 160 97 225 353), lower := (rows 67 38 140 56 273 160 64 128 256), losses := [] }

theorem u3161 : Upper (D 8) (R 8) [66,36,136,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3162 : PairBound 9 := { available := 161, camps := [], pairs := [(1,6)], upper := (rows 67 38 140 56 336 33 225 161 417), lower := (rows 67 38 140 56 336 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 16 33 0 161 289), good := (rows 419 422 142 446 272 417 0 128 256) }] }

theorem u3162 : Upper (D 8) (R 8) [66,36,136,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3163 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 56 336 160 97 161 289), lower := (rows 67 38 140 56 336 160 64 128 256), losses := [] }

theorem u3163 : Upper (D 8) (R 8) [66,36,136,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3164 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 67 38 140 265 49 48 224 224 480), lower := (rows 67 38 140 265 49 48 64 128 256), losses := [] }

theorem u3164 : Upper (D 8) (R 8) [66,36,136,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3164 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3165 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 265 49 96 240 176 432), lower := (rows 67 38 140 265 49 96 64 128 256), losses := [] }

theorem u3165 : Upper (D 8) (R 8) [66,36,136,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3166 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 265 49 160 112 240 368), lower := (rows 67 38 140 265 49 160 64 128 256), losses := [] }

theorem u3166 : Upper (D 8) (R 8) [66,36,136,257,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3167 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 38 140 265 112 33 240 176 432), lower := (rows 67 38 140 265 112 33 64 128 256), losses := [] }

theorem u3167 : Upper (D 8) (R 8) [66,36,136,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3168 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 140 265 112 48 225 161 417), lower := (rows 67 38 140 265 112 48 64 128 256), losses := [] }

theorem u3168 : Upper (D 8) (R 8) [66,36,136,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3168 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3169 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 265 112 160 113 177 305), lower := (rows 67 38 140 265 112 160 64 128 256), losses := [] }

theorem u3169 : Upper (D 8) (R 8) [66,36,136,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3170 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 140 265 176 33 112 240 368), lower := (rows 67 38 140 265 176 33 64 128 256), losses := [] }

theorem u3170 : Upper (D 8) (R 8) [66,36,136,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3171 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 140 265 176 48 97 225 353), lower := (rows 67 38 140 265 176 48 64 128 256), losses := [] }

theorem u3171 : Upper (D 8) (R 8) [66,36,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3171 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3172 : Route 9 := (fun mask => (mask,id))

def c3172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3172 : Upper (D 8) (R 8) [66,36,136,257,160,64] 13 := by
  apply FastRouting.sound _ _ [66,36,136,257,160,64] 13 (by decide) (choices 1) [1,16,32] r3172 c3172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u408
  · exact u409
  · exact u410

def b3173 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 140 265 208 33 112 176 304), lower := (rows 67 38 140 265 208 33 64 128 256), losses := [] }

theorem u3173 : Upper (D 8) (R 8) [66,36,136,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3174 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 140 265 208 48 97 161 289), lower := (rows 67 38 140 265 208 48 64 128 256), losses := [] }

theorem u3174 : Upper (D 8) (R 8) [66,36,136,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3174 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3175 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 280 49 33 224 224 480), lower := (rows 67 38 140 280 49 33 64 128 256), losses := [] }

theorem u3175 : Upper (D 8) (R 8) [66,36,136,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3176 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 280 49 96 225 161 417), lower := (rows 67 38 140 280 49 96 64 128 256), losses := [] }

theorem u3176 : Upper (D 8) (R 8) [66,36,136,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3177 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 280 49 160 97 225 353), lower := (rows 67 38 140 280 49 160 64 128 256), losses := [] }

theorem u3177 : Upper (D 8) (R 8) [66,36,136,272,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3178 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 38 140 280 112 33 225 161 417), lower := (rows 67 38 140 280 112 33 64 128 256), losses := [] }

theorem u3178 : Upper (D 8) (R 8) [66,36,136,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3179 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 280 112 160 97 161 289), lower := (rows 67 38 140 280 112 160 64 128 256), losses := [] }

theorem u3179 : Upper (D 8) (R 8) [66,36,136,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3179
end Delivery.IrregularNine14.P08
