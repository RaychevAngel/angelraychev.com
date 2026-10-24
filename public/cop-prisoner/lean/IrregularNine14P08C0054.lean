import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0007

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3240 : PairBound 9 := { available := 49, camps := [], pairs := [(4,0)], upper := (rows 67 38 268 137 176 96 113 177 305), lower := (rows 67 38 268 137 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 97 64 128 256), good := (rows 98 38 284 184 176 96 96 128 256) }] }

theorem u3240 : Upper (D 8) (R 8) [66,36,264,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3241 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 268 137 208 33 112 176 304), lower := (rows 67 38 268 137 208 33 64 128 256), losses := [] }

theorem u3241 : Upper (D 8) (R 8) [66,36,264,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3242 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 268 137 208 48 97 161 289), lower := (rows 67 38 268 137 208 48 64 128 256), losses := [] }

theorem u3242 : Upper (D 8) (R 8) [66,36,264,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3242 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3243 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 268 152 49 33 224 224 480), lower := (rows 67 38 268 152 49 33 64 128 256), losses := [] }

theorem u3243 : Upper (D 8) (R 8) [66,36,264,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3244 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 152 49 96 225 161 417), lower := (rows 67 38 268 152 49 96 64 128 256), losses := [] }

theorem u3244 : Upper (D 8) (R 8) [66,36,264,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3245 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 152 49 160 97 225 353), lower := (rows 67 38 268 152 49 160 64 128 256), losses := [] }

theorem u3245 : Upper (D 8) (R 8) [66,36,264,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3246 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 38 268 152 112 33 225 161 417), lower := (rows 67 38 268 152 112 33 64 128 256), losses := [] }

theorem u3246 : Upper (D 8) (R 8) [66,36,264,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3247 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 152 112 160 97 161 289), lower := (rows 67 38 268 152 112 160 64 128 256), losses := [] }

theorem u3247 : Upper (D 8) (R 8) [66,36,264,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3248 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 268 168 49 33 208 208 464), lower := (rows 67 38 268 168 49 33 64 128 256), losses := [] }

theorem u3248 : Upper (D 8) (R 8) [66,36,264,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3249 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 38 268 168 49 48 193 193 449), lower := (rows 67 38 268 168 49 48 64 128 256), losses := [] }

theorem u3249 : Upper (D 8) (R 8) [66,36,264,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3249 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3250 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 168 49 96 209 145 401), lower := (rows 67 38 268 168 49 96 64 128 256), losses := [] }

theorem u3250 : Upper (D 8) (R 8) [66,36,264,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3251 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 168 49 160 81 209 337), lower := (rows 67 38 268 168 49 160 64 128 256), losses := [] }

theorem u3251 : Upper (D 8) (R 8) [66,36,264,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3252 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 38 268 168 112 33 209 145 401), lower := (rows 67 38 268 168 112 33 64 128 256), losses := [] }

theorem u3252 : Upper (D 8) (R 8) [66,36,264,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3253 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 38 268 168 112 48 193 129 385), lower := (rows 67 38 268 168 112 48 64 128 256), losses := [] }

theorem u3253 : Upper (D 8) (R 8) [66,36,264,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3253 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3254 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 168 112 160 81 145 273), lower := (rows 67 38 268 168 112 160 64 128 256), losses := [] }

theorem u3254 : Upper (D 8) (R 8) [66,36,264,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3255 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 268 168 145 33 112 240 368), lower := (rows 67 38 268 168 145 33 64 128 256), losses := [] }

theorem u3255 : Upper (D 8) (R 8) [66,36,264,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3256 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 268 168 145 48 97 225 353), lower := (rows 67 38 268 168 145 48 64 128 256), losses := [] }

theorem u3256 : Upper (D 8) (R 8) [66,36,264,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3256 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3257 : PairBound 9 := { available := 49, camps := [], pairs := [(3,0)], upper := (rows 67 38 268 168 145 96 113 177 305), lower := (rows 67 38 268 168 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 97 64 128 256), good := (rows 98 38 268 168 184 96 96 128 256) }] }

theorem u3257 : Upper (D 8) (R 8) [66,36,264,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3258 : Route 9 := (fun mask => (mask,id))

def c3258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3258 : Upper (D 8) (R 8) [66,36,264,160,192,1] 13 := by
  apply FastRouting.sound _ _ [66,36,264,160,192,1] 13 (by decide) (choices 1) [1,16,32] r3258 c3258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u430
  · exact u431
  · exact u432

def b3259 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 268 168 208 48 97 161 289), lower := (rows 67 38 268 168 208 48 64 128 256), losses := [] }

theorem u3259 : Upper (D 8) (R 8) [66,36,264,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3259 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3260 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 67 38 388 25 56 33 224 224 480), lower := (rows 67 38 388 25 56 33 64 128 256), losses := [] }

theorem u3260 : Upper (D 8) (R 8) [66,36,384,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3261 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 56, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 388 25 56 96 225 161 417), lower := (rows 67 38 388 25 56 96 64 128 256), losses := [] }

theorem u3261 : Upper (D 8) (R 8) [66,36,384,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3262 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 25 56 160 97 225 353), lower := (rows 67 38 388 25 56 160 64 128 256), losses := [] }

theorem u3262 : Upper (D 8) (R 8) [66,36,384,17,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3263 : Route 9 := (fun mask => (mask,id))

def c3263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3263 : Upper (D 8) (R 8) [66,36,384,17,160,1] 13 := by
  apply FastRouting.sound _ _ [66,36,384,17,160,1] 13 (by decide) (choices 1) [8,32] r3263 c3263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u433
  · exact u434

def b3264 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 388 25 176 40 97 225 353), lower := (rows 67 38 388 25 176 40 64 128 256), losses := [] }

theorem u3264 : Upper (D 8) (R 8) [66,36,384,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3264 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3265 : Route 9 := (fun mask => (mask,id))

def c3265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3265 : Upper (D 8) (R 8) [66,36,384,17,160,64] 13 := by
  apply FastRouting.sound _ _ [66,36,384,17,160,64] 13 (by decide) (choices 1) [1,8,32] r3265 c3265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u435
  · exact u436
  · exact u437

def b3266 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 388 41 88 33 240 176 432), lower := (rows 67 38 388 41 88 33 64 128 256), losses := [] }

theorem u3266 : Upper (D 8) (R 8) [66,36,384,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3267 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 38 388 41 88 48 225 161 417), lower := (rows 67 38 388 41 88 48 64 128 256), losses := [] }

theorem u3267 : Upper (D 8) (R 8) [66,36,384,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3267 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3268 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 89, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 41 88 160 113 177 305), lower := (rows 67 38 388 41 88 160 64 128 256), losses := [] }

theorem u3268 : Upper (D 8) (R 8) [66,36,384,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3269 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 388 41 112 33 216 152 408), lower := (rows 67 38 388 41 112 33 64 128 256), losses := [] }

theorem u3269 : Upper (D 8) (R 8) [66,36,384,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3270 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 38 388 41 112 40 209 145 401), lower := (rows 67 38 388 41 112 40 64 128 256), losses := [] }

theorem u3270 : Upper (D 8) (R 8) [66,36,384,33,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3270 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3271 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 38 388 41 112 48 201 137 393), lower := (rows 67 38 388 41 112 48 64 128 256), losses := [] }

theorem u3271 : Upper (D 8) (R 8) [66,36,384,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3271 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3272 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 89, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 41 112 160 89 153 281), lower := (rows 67 38 388 41 112 160 64 128 256), losses := [] }

theorem u3272 : Upper (D 8) (R 8) [66,36,384,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3273 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 388 41 152 33 112 240 368), lower := (rows 67 38 388 41 152 33 64 128 256), losses := [] }

theorem u3273 : Upper (D 8) (R 8) [66,36,384,33,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3274 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 38 388 41 152 48 97 225 353), lower := (rows 67 38 388 41 152 48 64 128 256), losses := [] }

theorem u3274 : Upper (D 8) (R 8) [66,36,384,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3274 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3275 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 41 152 96 113 177 305), lower := (rows 67 38 388 41 152 96 64 128 256), losses := [] }

theorem u3275 : Upper (D 8) (R 8) [66,36,384,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3276 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 388 41 176 33 88 216 344), lower := (rows 67 38 388 41 176 33 64 128 256), losses := [] }

theorem u3276 : Upper (D 8) (R 8) [66,36,384,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3277 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 38 388 41 176 40 81 209 337), lower := (rows 67 38 388 41 176 40 64 128 256), losses := [] }

theorem u3277 : Upper (D 8) (R 8) [66,36,384,33,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3277 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3278 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 67 38 388 41 176 48 73 201 329), lower := (rows 67 38 388 41 176 48 64 128 256), losses := [] }

theorem u3278 : Upper (D 8) (R 8) [66,36,384,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3278 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3279 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 41 176 96 89 153 281), lower := (rows 67 38 388 41 176 96 64 128 256), losses := [] }

theorem u3279 : Upper (D 8) (R 8) [66,36,384,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3280 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 388 41 208 33 120 184 312), lower := (rows 67 38 388 41 208 33 64 128 256), losses := [] }

theorem u3280 : Upper (D 8) (R 8) [66,36,384,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3281 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 38 388 41 208 40 113 177 305), lower := (rows 67 38 388 41 208 40 64 128 256), losses := [] }

theorem u3281 : Upper (D 8) (R 8) [66,36,384,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3281 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3282 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 38 388 41 208 48 105 169 297), lower := (rows 67 38 388 41 208 48 64 128 256), losses := [] }

theorem u3282 : Upper (D 8) (R 8) [66,36,384,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3282 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3283 : Route 9 := (fun mask => (mask,id))

def c3283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3283 : Upper (D 8) (R 8) [66,36,384,48,192,1] 13 := by
  apply FastRouting.sound _ _ [66,36,384,48,192,1] 13 (by decide) (choices 1) [1,8,32] r3283 c3283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u438
  · exact u439
  · exact u440

def b3284 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 388 56 208 40 97 161 289), lower := (rows 67 38 388 56 208 40 64 128 256), losses := [] }

theorem u3284 : Upper (D 8) (R 8) [66,36,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3284 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3285 : Route 9 := (fun mask => (mask,id))

def c3285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3285 : Upper (D 8) (R 8) [66,36,384,80,160,1] 13 := by
  apply FastRouting.sound _ _ [66,36,384,80,160,1] 13 (by decide) (choices 1) [1,8,32] r3285 c3285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u441
  · exact u442
  · exact u443

def b3286 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 388 88 176 40 97 161 289), lower := (rows 67 38 388 88 176 40 64 128 256), losses := [] }

theorem u3286 : Upper (D 8) (R 8) [66,36,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3286 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3287 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 388 104 152 33 113 177 305), lower := (rows 67 38 388 104 152 33 64 128 256), losses := [] }

theorem u3287 : Upper (D 8) (R 8) [66,36,384,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3288 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 388 104 152 48 97 161 289), lower := (rows 67 38 388 104 152 48 64 128 256), losses := [] }

theorem u3288 : Upper (D 8) (R 8) [66,36,384,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3288 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3289 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 388 104 176 33 89 153 281), lower := (rows 67 38 388 104 176 33 64 128 256), losses := [] }

theorem u3289 : Upper (D 8) (R 8) [66,36,384,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3290 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 38 388 104 176 40 81 145 273), lower := (rows 67 38 388 104 176 40 64 128 256), losses := [] }

theorem u3290 : Upper (D 8) (R 8) [66,36,384,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3290 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3291 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 67 38 388 104 176 48 73 137 265), lower := (rows 67 38 388 104 176 48 64 128 256), losses := [] }

theorem u3291 : Upper (D 8) (R 8) [66,36,384,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3291 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3292 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 104 176 33 356 420 292), lower := (rows 67 131 28 104 176 33 64 128 256), losses := [] }

theorem u3292 : Upper (D 8) (R 8) [66,129,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3293 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 131 28 104 176 36 353 417 289), lower := (rows 67 131 28 104 176 36 64 128 256), losses := [] }

theorem u3293 : Upper (D 8) (R 8) [66,129,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3293 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3294 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 131 28 104 176 288 101 165 293), lower := (rows 67 131 28 104 176 288 64 128 256), losses := [] }

theorem u3294 : Upper (D 8) (R 8) [66,129,24,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3294 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3295 : PairBound 9 := { available := 164, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 104 304 33 228 164 420), lower := (rows 67 131 28 104 304 33 64 128 256), losses := [] }

theorem u3295 : Upper (D 8) (R 8) [66,129,24,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3296 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 131 28 104 304 36 225 161 417), lower := (rows 67 131 28 104 304 36 64 128 256), losses := [] }

theorem u3296 : Upper (D 8) (R 8) [66,129,24,96,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3296 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3297 : PairBound 9 := { available := 37, camps := [], pairs := [(3,0)], upper := (rows 67 131 28 104 304 160 101 165 293), lower := (rows 67 131 28 104 304 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 16 162 64 128 256), good := (rows 106 170 28 104 304 160 64 160 256) }] }

theorem u3297 : Upper (D 8) (R 8) [66,129,24,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3298 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 28 104 400 33 100 164 292), lower := (rows 67 131 28 104 400 33 64 128 256), losses := [] }

theorem u3298 : Upper (D 8) (R 8) [66,129,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3299 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 28 104 400 36 97 161 289), lower := (rows 67 131 28 104 400 36 64 128 256), losses := [] }

theorem u3299 : Upper (D 8) (R 8) [66,129,24,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3299 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3299
end Delivery.IrregularNine14.P08
