import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0006
import IrregularNine14P09C0007

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3240 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,7)], upper := (rows 7 35 196 73 280 160 368 432 304), lower := (rows 7 35 196 73 280 160 64 128 256), losses := [] }

theorem u3240 : Upper (D 9) (R 9) [6,33,192,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3240 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3241 : Route 9 := (fun mask => (mask,id))

def c3241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3241 : Upper (D 9) (R 9) [6,33,192,65,264,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,264,256] 13 (by decide) (choices 1) [16,32,128] r3241 c3241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u375
  · exact u376
  · exact u377

def b3242 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 196 73 304 40 464 400 400), lower := (rows 7 35 196 73 304 40 64 128 256), losses := [] }

theorem u3242 : Upper (D 9) (R 9) [6,33,192,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3242 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3243 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 35 196 73 304 48 456 392 392), lower := (rows 7 35 196 73 304 48 64 128 256), losses := [] }

theorem u3243 : Upper (D 9) (R 9) [6,33,192,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3243 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3244 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,7)], upper := (rows 7 35 196 73 304 160 344 408 280), lower := (rows 7 35 196 73 304 160 64 128 256), losses := [] }

theorem u3244 : Upper (D 9) (R 9) [6,33,192,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3244 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3245 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 35 196 73 304 288 216 152 408), lower := (rows 7 35 196 73 304 288 64 128 256), losses := [] }

theorem u3245 : Upper (D 9) (R 9) [6,33,192,65,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3245 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3246 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 196 73 400 40 368 432 304), lower := (rows 7 35 196 73 400 40 64 128 256), losses := [] }

theorem u3246 : Upper (D 9) (R 9) [6,33,192,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3246 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3247 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,6)], upper := (rows 7 35 196 73 400 48 360 424 296), lower := (rows 7 35 196 73 400 48 64 128 256), losses := [] }

theorem u3247 : Upper (D 9) (R 9) [6,33,192,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3247 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3248 : Route 9 := (fun mask => (mask,id))

def c3248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3248 : Upper (D 9) (R 9) [6,33,192,65,384,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,384,256] 13 (by decide) (choices 1) [8,16,32] r3248 c3248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u378
  · exact u379
  · exact u380

def b3249 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 4, region := 332, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 7 35 196 88 176 33 328 392 264), lower := (rows 7 35 196 88 176 33 64 128 256), losses := [] }

theorem u3249 : Upper (D 9) (R 9) [6,33,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3249 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3250 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 35 196 88 176 40 321 385 257), lower := (rows 7 35 196 88 176 40 64 128 256), losses := [] }

theorem u3250 : Upper (D 9) (R 9) [6,33,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3250 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3251 : Route 9 := (fun mask => (mask,id))

def c3251 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3251 : Upper (D 9) (R 9) [6,33,192,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,160,256] 13 (by decide) (choices 1) [1,8,256] r3251 c3251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u381
  · exact u382
  · exact u383

def r3252 : Route 9 := (fun mask => (mask,id))

def c3252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3252 : Upper (D 9) (R 9) [6,33,192,80,257,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,257,8] 13 (by decide) (choices 1) [32,128,256] r3252 c3252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u384
  · exact u385
  · exact u386

def b3253 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 7 35 196 88 273 160 360 424 296), lower := (rows 7 35 196 88 273 160 64 128 256), losses := [] }

theorem u3253 : Upper (D 9) (R 9) [6,33,192,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3253 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3254 : Route 9 := (fun mask => (mask,id))

def c3254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3254 : Upper (D 9) (R 9) [6,33,192,80,257,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,257,256] 13 (by decide) (choices 1) [8,32,128] r3254 c3254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u387
  · exact u388
  · exact u389

def b3255 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 452, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 7 35 196 88 280 33 480 416 416), lower := (rows 7 35 196 88 280 33 64 128 256), losses := [] }

theorem u3255 : Upper (D 9) (R 9) [6,33,192,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3255 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3256 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 },{ cop := 2, region := 35, targets := 256 }], pairs := [(0,6),(0,8),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 88 280 160 353 417 289), lower := (rows 7 35 196 88 280 160 64 128 256), losses := [] }

theorem u3256 : Upper (D 9) (R 9) [6,33,192,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3256 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3257 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(0,8),(1,6),(1,8),(2,8)], upper := (rows 7 35 196 88 280 288 225 161 417), lower := (rows 7 35 196 88 280 288 64 128 256), losses := [] }

theorem u3257 : Upper (D 9) (R 9) [6,33,192,80,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3257 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3258 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 196 88 304 33 456 392 392), lower := (rows 7 35 196 88 304 33 64 128 256), losses := [] }

theorem u3258 : Upper (D 9) (R 9) [6,33,192,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3258 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3259 : Route 9 := (fun mask => (mask,id))

def c3259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3259 : Upper (D 9) (R 9) [6,33,192,80,288,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,288,8] 13 (by decide) (choices 1) [1,128,256] r3259 c3259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u390
  · exact u391
  · exact u392

def b3260 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 7 35 196 88 304 160 329 393 265), lower := (rows 7 35 196 88 304 160 64 128 256), losses := [] }

theorem u3260 : Upper (D 9) (R 9) [6,33,192,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3260 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3261 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 35 196 88 304 288 201 137 393), lower := (rows 7 35 196 88 304 288 64 128 256), losses := [] }

theorem u3261 : Upper (D 9) (R 9) [6,33,192,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3261 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3262 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 196 88 400 33 360 424 296), lower := (rows 7 35 196 88 400 33 64 128 256), losses := [] }

theorem u3262 : Upper (D 9) (R 9) [6,33,192,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3262 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3263 : Route 9 := (fun mask => (mask,id))

def c3263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3263 : Upper (D 9) (R 9) [6,33,192,80,384,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,384,8] 13 (by decide) (choices 1) [1,32,256] r3263 c3263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u393
  · exact u394
  · exact u395

def r3264 : Route 9 := (fun mask => (mask,id))

def c3264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3264 : Upper (D 9) (R 9) [6,33,192,80,384,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,384,256] 13 (by decide) (choices 1) [1,8,32] r3264 c3264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u396
  · exact u397
  · exact u398

def b3265 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 196 104 273 40 464 400 400), lower := (rows 7 35 196 104 273 40 64 128 256), losses := [] }

theorem u3265 : Upper (D 9) (R 9) [6,33,192,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3265 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3266 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 34, targets := 448 },{ cop := 1, region := 460, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0)], upper := (rows 7 35 196 104 273 48 456 392 392), lower := (rows 7 35 196 104 273 48 64 128 256), losses := [] }

theorem u3266 : Upper (D 9) (R 9) [6,33,192,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3266 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3267 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,7)], upper := (rows 7 35 196 104 273 160 344 408 280), lower := (rows 7 35 196 104 273 160 64 128 256), losses := [] }

theorem u3267 : Upper (D 9) (R 9) [6,33,192,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3267 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3268 : Route 9 := (fun mask => (mask,id))

def c3268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3268 : Upper (D 9) (R 9) [6,33,192,96,257,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,257,256] 13 (by decide) (choices 1) [8,16,128] r3268 c3268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u399
  · exact u400
  · exact u401

def b3269 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 35 196 104 280 33 464 400 400), lower := (rows 7 35 196 104 280 33 64 128 256), losses := [] }

theorem u3269 : Upper (D 9) (R 9) [6,33,192,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3269 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3270 : Route 9 := (fun mask => (mask,id))

def c3270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3270 : Upper (D 9) (R 9) [6,33,192,96,264,16] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264,16] 13 (by decide) (choices 1) [1,128,256] r3270 c3270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u402
  · exact u403
  · exact u404

def b3271 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,7)], upper := (rows 7 35 196 104 280 160 337 401 273), lower := (rows 7 35 196 104 280 160 64 128 256), losses := [] }

theorem u3271 : Upper (D 9) (R 9) [6,33,192,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3271 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3272 : Route 9 := (fun mask => (mask,id))

def c3272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3272 : Upper (D 9) (R 9) [6,33,192,96,264,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264,256] 13 (by decide) (choices 1) [1,16,128] r3272 c3272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u405
  · exact u406
  · exact u407

def b3273 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 35 196 104 400 33 344 408 280), lower := (rows 7 35 196 104 400 33 64 128 256), losses := [] }

theorem u3273 : Upper (D 9) (R 9) [6,33,192,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3273 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3274 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 196 104 400 40 337 401 273), lower := (rows 7 35 196 104 400 40 64 128 256), losses := [] }

theorem u3274 : Upper (D 9) (R 9) [6,33,192,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3274 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3275 : Route 9 := (fun mask => (mask,id))

def c3275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3275 : Upper (D 9) (R 9) [6,33,192,96,384,16] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,384,16] 13 (by decide) (choices 1) [1,8,256] r3275 c3275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u408
  · exact u409
  · exact u410

def r3276 : Route 9 := (fun mask => (mask,id))

def c3276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3276 : Upper (D 9) (R 9) [6,33,192,96,384,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,384,256] 13 (by decide) (choices 1) [1,8,16] r3276 c3276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u411
  · exact u412
  · exact u413

def b3277 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 196 265 304 40 208 208 464), lower := (rows 7 35 196 265 304 40 64 128 256), losses := [] }

theorem u3277 : Upper (D 9) (R 9) [6,33,192,257,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3277 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3278 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 35 196 265 304 48 200 200 456), lower := (rows 7 35 196 265 304 48 64 128 256), losses := [] }

theorem u3278 : Upper (D 9) (R 9) [6,33,192,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3278 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3279 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 196 265 304 96 216 152 408), lower := (rows 7 35 196 265 304 96 64 128 256), losses := [] }

theorem u3279 : Upper (D 9) (R 9) [6,33,192,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3279 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3280 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 1, region := 468, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0)], upper := (rows 7 35 196 265 336 40 240 176 432), lower := (rows 7 35 196 265 336 40 64 128 256), losses := [] }

theorem u3280 : Upper (D 9) (R 9) [6,33,192,257,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3280 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3281 : Route 9 := (fun mask => (mask,id))

def c3281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3281 : Upper (D 9) (R 9) [6,33,192,257,320,16] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257,320,16] 13 (by decide) (choices 1) [8,32,128] r3281 c3281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u414
  · exact u415
  · exact u416

def b3282 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 7 35 196 265 336 160 120 184 312), lower := (rows 7 35 196 265 336 160 64 128 256), losses := [] }

theorem u3282 : Upper (D 9) (R 9) [6,33,192,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3282 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3283 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 196 296 336 33 216 152 408), lower := (rows 7 35 196 296 336 33 64 128 256), losses := [] }

theorem u3283 : Upper (D 9) (R 9) [6,33,192,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3283 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3284 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 196 296 336 40 209 145 401), lower := (rows 7 35 196 296 336 40 64 128 256), losses := [] }

theorem u3284 : Upper (D 9) (R 9) [6,33,192,288,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3284 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3285 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 7 35 196 296 336 48 201 137 393), lower := (rows 7 35 196 296 336 48 64 128 256), losses := [] }

theorem u3285 : Upper (D 9) (R 9) [6,33,192,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3285 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3286 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 7 35 196 296 336 160 89 153 281), lower := (rows 7 35 196 296 336 160 64 128 256), losses := [] }

theorem u3286 : Upper (D 9) (R 9) [6,33,192,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3286 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3287 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 196 328 400 33 120 184 312), lower := (rows 7 35 196 328 400 33 64 128 256), losses := [] }

theorem u3287 : Upper (D 9) (R 9) [6,33,192,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3287 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3288 : Route 9 := (fun mask => (mask,id))

def c3288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3288 : Upper (D 9) (R 9) [6,33,192,320,384,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,320,384,8] 13 (by decide) (choices 1) [1,16,32] r3288 c3288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u417
  · exact u418
  · exact u419

def b3289 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,5),(4,6)], upper := (rows 7 42 52 73 145 96 448 384 384), lower := (rows 7 42 52 73 145 96 64 128 256), losses := [] }

theorem u3289 : Upper (D 9) (R 9) [6,40,48,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3289 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3290 : Route 9 := (fun mask => (mask,id))

def c3290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3290 : Upper (D 9) (R 9) [6,40,48,65,129,256] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,129,256] 13 (by decide) (choices 1) [128,256] r3290 c3290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u420
  · exact u421

def b3291 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 42 52 73 208 33 448 384 384), lower := (rows 7 42 52 73 208 33 64 128 256), losses := [] }

theorem u3291 : Upper (D 9) (R 9) [6,40,48,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3291 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3292 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 42 52 73 208 160 321 385 257), lower := (rows 7 42 52 73 208 160 64 128 256), losses := [] }

theorem u3292 : Upper (D 9) (R 9) [6,40,48,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3292 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3293 : Route 9 := (fun mask => (mask,id))

def c3293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3293 : Upper (D 9) (R 9) [6,40,48,65,192,256] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,192,256] 13 (by decide) (choices 1) [1,128,256] r3293 c3293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u422
  · exact u423
  · exact u424

def b3294 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(3,5),(4,5)], upper := (rows 7 42 52 73 400 33 448 448 448), lower := (rows 7 42 52 73 400 33 64 128 256), losses := [] }

theorem u3294 : Upper (D 9) (R 9) [6,40,48,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3294 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3295 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6),(4,6)], upper := (rows 7 42 52 73 400 96 449 385 385), lower := (rows 7 42 52 73 400 96 64 128 256), losses := [] }

theorem u3295 : Upper (D 9) (R 9) [6,40,48,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3295 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3296 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(3,7)], upper := (rows 7 42 52 73 400 160 321 449 321), lower := (rows 7 42 52 73 400 160 64 128 256), losses := [] }

theorem u3296 : Upper (D 9) (R 9) [6,40,48,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3296 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m3297_256 : Upper (D 9) (R 9) [6,40,48,192,320,1,256] 13 :=
  permutation_upper _ _ _ [6,40,48,192,320,1,128] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u426

def r3297 : Route 9 := (fun mask => (mask,id))

def c3297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3297 : Upper (D 9) (R 9) [6,40,48,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320,1] 13 (by decide) (choices 1) [1,128,256] r3297 c3297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u425
  · exact u426
  · exact m3297_256

def b3298 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 7 42 52 200 336 160 321 385 257), lower := (rows 7 42 52 200 336 160 64 128 256), losses := [] }

theorem u3298 : Upper (D 9) (R 9) [6,40,48,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3298 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3299 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 3, region := 418, targets := 1 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,0),(1,6),(2,0),(3,7),(4,6)], upper := (rows 7 42 84 73 145 160 352 416 288), lower := (rows 7 42 84 73 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 16 32 98 0 290), good := (rows 335 362 84 73 25 352 64 0 256) }] }

theorem u3299 : Upper (D 9) (R 9) [6,40,80,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3299 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3299
end Delivery.IrregularNine14.P09
