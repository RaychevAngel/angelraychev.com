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

def b3240 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 7 290 196 26 112 33 72 129 385), lower := (rows 7 290 196 26 112 33 72 128 256), losses := [] }

theorem u3240 : Upper (D 7) (R 7) [6,288,192,18,96,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3240 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3241 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 290 196 26 112 33 192 137 265), lower := (rows 7 290 196 26 112 33 192 128 256), losses := [] }

theorem u3241 : Upper (D 7) (R 7) [6,288,192,18,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3242 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 7 290 196 56 81 160 65 138 266), lower := (rows 7 290 196 56 81 160 65 128 256), losses := [] }

theorem u3242 : Upper (D 7) (R 7) [6,288,192,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3243 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 4, region := 172, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 290 196 56 81 160 66 137 265), lower := (rows 7 290 196 56 81 160 66 128 256), losses := [] }

theorem u3243 : Upper (D 7) (R 7) [6,288,192,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3244 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 196 56 81 160 72 131 259), lower := (rows 7 290 196 56 81 160 72 128 256), losses := [] }

theorem u3244 : Upper (D 7) (R 7) [6,288,192,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3244 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3245 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 120, targets := 128 },{ cop := 3, region := 386, targets := 65 }], pairs := [(1,0),(1,6),(3,7),(4,7)], upper := (rows 7 290 196 56 82 33 65 136 392), lower := (rows 7 290 196 56 82 33 65 128 256), losses := [] }

theorem u3245 : Upper (D 7) (R 7) [6,288,192,48,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3246 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 7 290 196 56 82 33 72 129 385), lower := (rows 7 290 196 56 82 33 72 128 256), losses := [] }

theorem u3246 : Upper (D 7) (R 7) [6,288,192,48,66,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3246 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3247 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 290 196 56 82 33 192 137 265), lower := (rows 7 290 196 56 82 33 192 128 256), losses := [] }

theorem u3247 : Upper (D 7) (R 7) [6,288,192,48,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3248 : Route 9 := (fun mask => (mask,id))

def c3248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3248 : Upper (D 7) (R 7) [6,288,192,48,66,128,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,48,66,128,1] 13 (by decide) (choices 1) [1,8] r3248 c3248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u198
  · exact u199

def b3249 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 7 290 196 56 82 160 72 129 257), lower := (rows 7 290 196 56 82 160 72 128 256), losses := [] }

theorem u3249 : Upper (D 7) (R 7) [6,288,192,48,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3249 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3250 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 196 73 146 33 72 176 304), lower := (rows 7 290 196 73 146 33 72 128 256), losses := [] }

theorem u3250 : Upper (D 7) (R 7) [6,288,192,65,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3250 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3251 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 196 73 146 33 80 168 296), lower := (rows 7 290 196 73 146 33 80 128 256), losses := [] }

theorem u3251 : Upper (D 7) (R 7) [6,288,192,65,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3251 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3252 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 104, targets := 130 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(3,1),(3,7),(4,6)], upper := (rows 7 290 196 73 146 33 96 152 280), lower := (rows 7 290 196 73 146 33 96 128 256), losses := [] }

theorem u3252 : Upper (D 7) (R 7) [6,288,192,65,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3253 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 196 73 146 40 65 176 304), lower := (rows 7 290 196 73 146 40 65 128 256), losses := [] }

theorem u3253 : Upper (D 7) (R 7) [6,288,192,65,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3253 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3254 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 290 196 73 146 40 80 161 289), lower := (rows 7 290 196 73 146 40 80 128 256), losses := [] }

theorem u3254 : Upper (D 7) (R 7) [6,288,192,65,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3254 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3255 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 104, targets := 130 },{ cop := 0, region := 144, targets := 32 }], pairs := [(3,1),(3,7),(4,5)], upper := (rows 7 290 196 73 146 40 96 145 273), lower := (rows 7 290 196 73 146 40 96 128 256), losses := [] }

theorem u3255 : Upper (D 7) (R 7) [6,288,192,65,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3255 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3256 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 290 196 73 146 48 65 168 296), lower := (rows 7 290 196 73 146 48 65 128 256), losses := [] }

theorem u3256 : Upper (D 7) (R 7) [6,288,192,65,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3256 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3257 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 290 196 73 146 48 72 161 289), lower := (rows 7 290 196 73 146 48 72 128 256), losses := [] }

theorem u3257 : Upper (D 7) (R 7) [6,288,192,65,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3257 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3258 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 132, targets := 34 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 7 290 196 73 146 48 96 137 265), lower := (rows 7 290 196 73 146 48 96 128 256), losses := [] }

theorem u3258 : Upper (D 7) (R 7) [6,288,192,65,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3258 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3259 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 2 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(4,1),(4,6)], upper := (rows 7 290 196 73 152 33 66 176 304), lower := (rows 7 290 196 73 152 33 66 128 256), losses := [] }

theorem u3259 : Upper (D 7) (R 7) [6,288,192,65,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3260 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 196 73 152 33 80 162 290), lower := (rows 7 290 196 73 152 33 80 128 256), losses := [] }

theorem u3260 : Upper (D 7) (R 7) [6,288,192,65,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3260 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3261 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 104, targets := 130 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(3,1),(3,7),(4,6)], upper := (rows 7 290 196 73 152 33 96 146 274), lower := (rows 7 290 196 73 152 33 96 128 256), losses := [] }

theorem u3261 : Upper (D 7) (R 7) [6,288,192,65,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3262 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 290 196 73 152 48 65 162 290), lower := (rows 7 290 196 73 152 48 65 128 256), losses := [] }

theorem u3262 : Upper (D 7) (R 7) [6,288,192,65,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3262 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3263 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 180, targets := 2 }], pairs := [(2,1),(3,5),(3,7)], upper := (rows 7 290 196 73 152 48 66 161 289), lower := (rows 7 290 196 73 152 48 66 128 256), losses := [] }

theorem u3263 : Upper (D 7) (R 7) [6,288,192,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3263 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3264 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 100, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 7 290 196 73 152 48 96 131 259), lower := (rows 7 290 196 73 152 48 96 128 256), losses := [] }

theorem u3264 : Upper (D 7) (R 7) [6,288,192,65,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3264 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3265 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 180, targets := 2 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(4,1),(4,6)], upper := (rows 7 290 196 73 176 33 66 152 280), lower := (rows 7 290 196 73 176 33 66 128 256), losses := [] }

theorem u3265 : Upper (D 7) (R 7) [6,288,192,65,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3266 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 196 73 176 33 72 146 274), lower := (rows 7 290 196 73 176 33 72 128 256), losses := [] }

theorem u3266 : Upper (D 7) (R 7) [6,288,192,65,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3266 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3267 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 196 73 176 33 80 138 266), lower := (rows 7 290 196 73 176 33 80 128 256), losses := [] }

theorem u3267 : Upper (D 7) (R 7) [6,288,192,65,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3267 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3268 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 196 73 176 40 65 146 274), lower := (rows 7 290 196 73 176 40 65 128 256), losses := [] }

theorem u3268 : Upper (D 7) (R 7) [6,288,192,65,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3268 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3269 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 180, targets := 2 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 7 290 196 73 176 40 66 145 273), lower := (rows 7 290 196 73 176 40 66 128 256), losses := [] }

theorem u3269 : Upper (D 7) (R 7) [6,288,192,65,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3269 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3270 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 290 196 73 176 40 80 131 259), lower := (rows 7 290 196 73 176 40 80 128 256), losses := [] }

theorem u3270 : Upper (D 7) (R 7) [6,288,192,65,160,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3270 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3271 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 290 196 74 152 33 65 176 304), lower := (rows 7 290 196 74 152 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 97 97 136 264), good := (rows 101 352 228 508 412 97 97 128 256) }] }

theorem u3271 : Upper (D 7) (R 7) [6,288,192,66,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3272 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 196 74 152 33 80 161 289), lower := (rows 7 290 196 74 152 33 80 128 256), losses := [] }

theorem u3272 : Upper (D 7) (R 7) [6,288,192,66,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3272 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3273 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 149, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 290 196 74 152 33 96 145 273), lower := (rows 7 290 196 74 152 33 96 128 256), losses := [] }

theorem u3273 : Upper (D 7) (R 7) [6,288,192,66,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3274 : Route 9 := (fun mask => (mask,id))

def c3274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3274 : Upper (D 7) (R 7) [6,288,192,66,136,16,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,66,136,16,1] 13 (by decide) (choices 1) [1,32] r3274 c3274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u200
  · exact u201

def b3275 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 149, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 196 74 152 48 96 129 257), lower := (rows 7 290 196 74 152 48 96 128 256), losses := [] }

theorem u3275 : Upper (D 7) (R 7) [6,288,192,66,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3275 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3276 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 72, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 290 196 74 176 33 65 152 280), lower := (rows 7 290 196 74 176 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 28 8 28 97 97 136 264), good := (rows 117 352 244 508 244 97 97 128 256) }] }

theorem u3276 : Upper (D 7) (R 7) [6,288,192,66,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3277 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 161 }], pairs := [(3,0),(3,5),(3,7)], upper := (rows 7 290 196 74 176 33 72 145 273), lower := (rows 7 290 196 74 176 33 72 128 256), losses := [] }

theorem u3277 : Upper (D 7) (R 7) [6,288,192,66,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3277 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3278 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 196 74 176 33 80 137 265), lower := (rows 7 290 196 74 176 33 80 128 256), losses := [] }

theorem u3278 : Upper (D 7) (R 7) [6,288,192,66,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3278 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3279 : Route 9 := (fun mask => (mask,id))

def c3279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3279 : Upper (D 7) (R 7) [6,288,192,66,160,8,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,66,160,8,1] 13 (by decide) (choices 1) [1,16] r3279 c3279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u202
  · exact u203

def b3280 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 290 196 74 176 40 80 129 257), lower := (rows 7 290 196 74 176 40 80 128 256), losses := [] }

theorem u3280 : Upper (D 7) (R 7) [6,288,192,66,160,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3280 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3281 : PairBound 9 := { available := 10, camps := [], pairs := [(2,1),(2,5),(3,1),(4,1)], upper := (rows 7 290 196 88 176 33 65 138 266), lower := (rows 7 290 196 88 176 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 29 20 97 97 128 256), good := (rows 125 352 252 124 252 105 105 128 256) },{ target := 5, region := (rows 1 2 20 24 16 0 97 128 256), good := (rows 71 322 196 92 220 65 65 128 256) }] }

theorem u3281 : Upper (D 7) (R 7) [6,288,192,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3282 : Route 9 := (fun mask => (mask,id))

def c3282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3282 : Upper (D 7) (R 7) [6,288,192,80,160,1,2] 13 := by
  apply FastRouting.sound _ _ [6,288,192,80,160,1,2] 13 (by decide) (choices 1) [1,8] r3282 c3282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u204
  · exact u205

def b3283 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 76, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 290 196 88 176 33 72 131 259), lower := (rows 7 290 196 88 176 33 72 128 256), losses := [] }

theorem u3283 : Upper (D 7) (R 7) [6,288,192,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3283 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3284 : Route 9 := (fun mask => (mask,id))

def c3284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3284 : Upper (D 7) (R 7) [6,288,192,80,160,2,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,80,160,2,1] 13 (by decide) (choices 1) [1,8] r3284 c3284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u206
  · exact u207

def b3285 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 76, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 290 196 88 176 34 72 129 257), lower := (rows 7 290 196 88 176 34 72 128 256), losses := [] }

theorem u3285 : Upper (D 7) (R 7) [6,288,192,80,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3285 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3286 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 149, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 35 21 74 146 288 96 192 448), lower := (rows 13 35 21 74 146 288 96 128 256), losses := [] }

theorem u3286 : Upper (D 7) (R 7) [12,33,17,66,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3286 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3287 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 21 74 146 288 192 224 352), lower := (rows 13 35 21 74 146 288 192 128 256), losses := [] }

theorem u3287 : Upper (D 7) (R 7) [12,33,17,66,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3287 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3288 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 13 35 21 74 274 160 96 192 448), lower := (rows 13 35 21 74 274 160 96 128 256), losses := [] }

theorem u3288 : Upper (D 7) (R 7) [12,33,17,66,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3289 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 13 35 21 74 274 160 192 224 352), lower := (rows 13 35 21 74 274 160 192 128 256), losses := [{ target := 5, region := (rows 17 2 20 10 16 0 224 128 256), good := (rows 13 75 21 74 287 192 192 192 256) }] }

theorem u3289 : Upper (D 7) (R 7) [12,33,17,66,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3290 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 21 74 304 160 66 192 448), lower := (rows 13 35 21 74 304 160 66 128 256), losses := [] }

theorem u3290 : Upper (D 7) (R 7) [12,33,17,66,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3291 : Route 9 := (fun mask => (mask,id))

def c3291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3291 : Upper (D 7) (R 7) [12,33,17,66,288,128,128] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,288,128,128] 13 (by decide) (choices 1) [2,64] r3291 c3291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u208
  · exact u209

def b3292 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 437, targets := 2 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 13 35 21 74 336 160 66 160 416), lower := (rows 13 35 21 74 336 160 66 128 256), losses := [] }

theorem u3292 : Upper (D 7) (R 7) [12,33,17,66,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3293 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 13 35 21 74 336 160 96 130 386), lower := (rows 13 35 21 74 336 160 96 128 256), losses := [] }

theorem u3293 : Upper (D 7) (R 7) [12,33,17,66,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3294 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0)], upper := (rows 13 35 21 74 336 160 192 162 290), lower := (rows 13 35 21 74 336 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 16 0 224 128 256), good := (rows 13 75 21 74 336 192 192 192 256) }] }

theorem u3294 : Upper (D 7) (R 7) [12,33,17,66,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3295 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 456, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 13 35 21 266 82 160 96 192 448), lower := (rows 13 35 21 266 82 160 96 128 256), losses := [] }

theorem u3295 : Upper (D 7) (R 7) [12,33,17,258,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3296 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 472, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 13 35 21 266 82 160 192 224 352), lower := (rows 13 35 21 266 82 160 192 128 256), losses := [{ target := 5, region := (rows 9 2 14 8 18 0 224 128 256), good := (rows 13 87 21 287 86 192 192 192 256) }] }

theorem u3296 : Upper (D 7) (R 7) [12,33,17,258,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3297 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 84, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 21 266 112 160 66 192 448), lower := (rows 13 35 21 266 112 160 66 128 256), losses := [] }

theorem u3297 : Upper (D 7) (R 7) [12,33,17,258,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3298 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 21 266 112 160 192 194 322), lower := (rows 13 35 21 266 112 160 192 128 256), losses := [] }

theorem u3298 : Upper (D 7) (R 7) [12,33,17,258,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3299 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5),(4,7)], upper := (rows 13 35 21 328 82 160 66 160 416), lower := (rows 13 35 21 328 82 160 66 128 256), losses := [] }

theorem u3299 : Upper (D 7) (R 7) [12,33,17,320,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3299
end Delivery.IrregularNine14.P07
