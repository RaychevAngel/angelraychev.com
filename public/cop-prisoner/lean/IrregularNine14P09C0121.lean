import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0067
import IrregularNine14P09C0068
import IrregularNine14P09C0069

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7260 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 152 280 484 452 452 452), lower := (rows 35 67 37 152 280 32 64 128 256), losses := [] }

theorem u7260 : Upper (D 9) (R 9) [34,65,33,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7260 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7261 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 152 336 428 460 396 396), lower := (rows 35 67 37 152 336 32 64 128 256), losses := [] }

theorem u7261 : Upper (D 9) (R 9) [34,65,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7261 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7262 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 67 37 200 400 316 348 412 284), lower := (rows 35 67 37 200 400 32 64 128 256), losses := [] }

theorem u7262 : Upper (D 9) (R 9) [34,65,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7262 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7263 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 8, targets := 416 },{ cop := 3, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(3,5),(3,7),(3,8)], upper := (rows 35 67 44 73 148 432 464 400 400), lower := (rows 35 67 44 73 148 32 64 128 256), losses := [] }

theorem u7263 : Upper (D 9) (R 9) [34,65,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7263 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7264 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 8, targets := 416 },{ cop := 3, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(3,5),(3,7),(3,8)], upper := (rows 35 67 44 73 400 436 468 404 404), lower := (rows 35 67 44 73 400 32 64 128 256), losses := [] }

theorem u7264 : Upper (D 9) (R 9) [34,65,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7264 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7265 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 364, targets := 1 }], pairs := [(0,6),(1,5),(2,0),(4,5),(4,6)], upper := (rows 35 67 44 76 145 432 464 400 400), lower := (rows 35 67 44 76 145 32 64 128 256), losses := [] }

theorem u7265 : Upper (D 9) (R 9) [34,65,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7265 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7266 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,5),(2,0),(4,5),(4,6)], upper := (rows 35 67 44 76 400 433 465 401 401), lower := (rows 35 67 44 76 400 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 10 16 32 64 128 256), good := (rows 46 78 44 76 400 32 64 128 256) }] }

theorem u7266 : Upper (D 9) (R 9) [34,65,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7266 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7267 : Route 9 := (fun mask => (mask,id))

def c7267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7267 : Upper (D 9) (R 9) [34,65,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,129] 13 (by decide) (choices 1) [4,128,256] r7267 c7267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4055
  · exact u4056
  · exact u4057

def r7268 : Route 9 := (fun mask => (mask,id))

def c7268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7268 : Upper (D 9) (R 9) [34,65,40,80,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,132] 13 (by decide) (choices 1) [1,128,256] r7268 c7268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4058
  · exact u4059
  · exact u4060

def r7269 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7269 : Upper (D 9) (R 9) [34,65,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,384] 13 (by decide) (choices 1) [1,4,128] r7269 c7269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4061
  · exact u4062
  · exact u4063

def r7270 : Route 9 := (fun mask => (mask,id))

def c7270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7270 : Upper (D 9) (R 9) [34,65,40,129,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,68] 13 (by decide) (choices 1) [16,128,256] r7270 c7270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4064
  · exact u4065
  · exact u4066

def b7271 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 4, region := 355, targets := 128 },{ cop := 2, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,5)], upper := (rows 35 67 44 137 148 368 336 464 336), lower := (rows 35 67 44 137 148 32 64 128 256), losses := [] }

theorem u7271 : Upper (D 9) (R 9) [34,65,40,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7271 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7272 : Route 9 := (fun mask => (mask,id))

def c7272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7272 : Upper (D 9) (R 9) [34,65,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,192] 13 (by decide) (choices 1) [4,16,256] r7272 c7272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4067
  · exact u4068
  · exact u4069

def r7273 : Route 9 := (fun mask => (mask,id))

def c7273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7273 : Upper (D 9) (R 9) [34,65,40,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,260] 13 (by decide) (choices 1) [16,64,128,256] r7273 c7273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4070
  · exact u4071
  · exact u4072
  · exact u4073

def r7274 : Route 9 := (fun mask => (mask,id))

def c7274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7274 : Upper (D 9) (R 9) [34,65,40,129,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,320] 13 (by decide) (choices 1) [4,16,128,256] r7274 c7274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4074
  · exact u4075
  · exact u4076
  · exact u4077

def r7275 : Route 9 := (fun mask => (mask,id))

def c7275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7275 : Upper (D 9) (R 9) [34,65,40,129,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,384] 13 (by decide) (choices 1) [4,16,64,256] r7275 c7275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4078
  · exact u4079
  · exact u4080
  · exact u4081

def b7276 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 384 },{ cop := 4, region := 428, targets := 1 }], pairs := [(1,5),(2,0),(4,5),(4,7),(4,8)], upper := (rows 35 67 44 140 81 432 464 400 400), lower := (rows 35 67 44 140 81 32 64 128 256), losses := [] }

theorem u7276 : Upper (D 9) (R 9) [34,65,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7276 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7277 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 364, targets := 1 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(2,0),(3,0),(4,5)], upper := (rows 35 67 44 140 145 368 336 464 336), lower := (rows 35 67 44 140 145 32 64 128 256), losses := [] }

theorem u7277 : Upper (D 9) (R 9) [34,65,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7277 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7278 : Route 9 := (fun mask => (mask,id))

def c7278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7278 : Upper (D 9) (R 9) [34,65,40,132,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,192] 13 (by decide) (choices 1) [1,16,256] r7278 c7278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4082
  · exact u4083
  · exact u4084

def r7279 : Route 9 := (fun mask => (mask,id))

def c7279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u7279 : Upper (D 9) (R 9) [34,65,40,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,257] 13 (by decide) (choices 1) [16,64,128,256] r7279 c7279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4085
  · exact u4086
  · exact u4087
  · exact u4088

def r7280 : Route 9 := (fun mask => (mask,id))

def c7280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7280 : Upper (D 9) (R 9) [34,65,40,132,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,320] 13 (by decide) (choices 1) [1,16,128,256] r7280 c7280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4089
  · exact u4090
  · exact u4091
  · exact u4092

def r7281 : Route 9 := (fun mask => (mask,id))

def c7281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7281 : Upper (D 9) (R 9) [34,65,40,132,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,384] 13 (by decide) (choices 1) [1,16,64,256] r7281 c7281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4093
  · exact u4094
  · exact u4095
  · exact u4096

def b7282 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 16, targets := 416 },{ cop := 4, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(4,5),(4,7),(4,8)], upper := (rows 35 67 44 152 81 420 452 388 388), lower := (rows 35 67 44 152 81 32 64 128 256), losses := [] }

theorem u7282 : Upper (D 9) (R 9) [34,65,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7282 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7283 : Route 9 := (fun mask => (mask,id))

def c7283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7283 : Upper (D 9) (R 9) [34,65,40,144,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,68] 13 (by decide) (choices 1) [1,128,256] r7283 c7283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4097
  · exact u4098
  · exact u4099

def b7284 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 96 }], pairs := [(0,7),(1,7),(2,7),(3,5),(3,6)], upper := (rows 35 67 44 152 145 356 324 452 324), lower := (rows 35 67 44 152 145 32 64 128 256), losses := [] }

theorem u7284 : Upper (D 9) (R 9) [34,65,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7284 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7285 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 67 44 152 148 353 321 449 321), lower := (rows 35 67 44 152 148 32 64 128 256), losses := [] }

theorem u7285 : Upper (D 9) (R 9) [34,65,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7285 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7286 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 67 44 152 208 293 325 389 261), lower := (rows 35 67 44 152 208 32 64 128 256), losses := [] }

theorem u7286 : Upper (D 9) (R 9) [34,65,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7286 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7287 : Route 9 := (fun mask => (mask,id))

def c7287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7287 : Upper (D 9) (R 9) [34,65,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,257] 13 (by decide) (choices 1) [4,64,128,256] r7287 c7287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4100
  · exact u4101
  · exact u4102
  · exact u4103

def r7288 : Route 9 := (fun mask => (mask,id))

def c7288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7288 : Upper (D 9) (R 9) [34,65,40,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,260] 13 (by decide) (choices 1) [1,64,128,256] r7288 c7288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4104
  · exact u4105
  · exact u4106
  · exact u4107

def r7289 : Route 9 := (fun mask => (mask,id))

def c7289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7289 : Upper (D 9) (R 9) [34,65,40,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,320] 13 (by decide) (choices 1) [1,4,128,256] r7289 c7289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4108
  · exact u4109
  · exact u4110
  · exact u4111

def b7290 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 35 67 44 152 400 357 325 453 325), lower := (rows 35 67 44 152 400 32 64 128 256), losses := [] }

theorem u7290 : Upper (D 9) (R 9) [34,65,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7290 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7291 : Route 9 := (fun mask => (mask,id))

def c7291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7291 : Upper (D 9) (R 9) [34,65,40,192,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,129] 13 (by decide) (choices 1) [4,16,256] r7291 c7291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4112
  · exact u4113
  · exact u4114

def r7292 : Route 9 := (fun mask => (mask,id))

def c7292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7292 : Upper (D 9) (R 9) [34,65,40,192,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,132] 13 (by decide) (choices 1) [1,16,256] r7292 c7292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4115
  · exact u4116
  · exact u4117

def r7293 : Route 9 := (fun mask => (mask,id))

def c7293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7293 : Upper (D 9) (R 9) [34,65,40,192,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,257] 13 (by decide) (choices 1) [4,16,128,256] r7293 c7293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4118
  · exact u4119
  · exact u4120
  · exact u4121

def r7294 : Route 9 := (fun mask => (mask,id))

def c7294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7294 : Upper (D 9) (R 9) [34,65,40,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,260] 13 (by decide) (choices 1) [1,16,128,256] r7294 c7294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4122
  · exact u4123
  · exact u4124
  · exact u4125

def r7295 : Route 9 := (fun mask => (mask,id))

def c7295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7295 : Upper (D 9) (R 9) [34,65,40,192,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,384] 13 (by decide) (choices 1) [1,4,16,256] r7295 c7295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4126
  · exact u4127
  · exact u4128
  · exact u4129

def b7296 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 16, targets := 416 },{ cop := 4, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(4,5),(4,7),(4,8)], upper := (rows 35 67 44 392 81 436 468 404 404), lower := (rows 35 67 44 392 81 32 64 128 256), losses := [] }

theorem u7296 : Upper (D 9) (R 9) [34,65,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7296 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7297 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7297 : Upper (D 9) (R 9) [34,65,40,384,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,68] 13 (by decide) (choices 1) [1,16,128] r7297 c7297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4130
  · exact u4131
  · exact u4132

def r7298 : Route 9 := (fun mask => (mask,id))

def c7298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7298 : Upper (D 9) (R 9) [34,65,40,384,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,129] 13 (by decide) (choices 1) [4,16,64,256] r7298 c7298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4133
  · exact u4134
  · exact u4135
  · exact u4136

def r7299 : Route 9 := (fun mask => (mask,id))

def c7299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7299 : Upper (D 9) (R 9) [34,65,40,384,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,132] 13 (by decide) (choices 1) [1,16,64,256] r7299 c7299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4137
  · exact u4138
  · exact u4139
  · exact u4140

def r7300 : Route 9 := (fun mask => (mask,id))

def c7300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7300 : Upper (D 9) (R 9) [34,65,40,384,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,192] 13 (by decide) (choices 1) [1,4,16,256] r7300 c7300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4141
  · exact u4142
  · exact u4143
  · exact u4144

def b7301 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 67 44 392 400 117 85 213 341), lower := (rows 35 67 44 392 400 32 64 128 256), losses := [] }

theorem u7301 : Upper (D 9) (R 9) [34,65,40,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7301 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7302 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 4, targets := 416 },{ cop := 2, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7),(2,8)], upper := (rows 35 67 69 140 176 312 344 408 280), lower := (rows 35 67 69 140 176 32 64 128 256), losses := [] }

theorem u7302 : Upper (D 9) (R 9) [34,65,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7302 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7303 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 4, targets := 416 },{ cop := 2, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7),(2,8)], upper := (rows 35 67 69 140 280 432 496 432 432), lower := (rows 35 67 69 140 280 32 64 128 256), losses := [] }

theorem u7303 : Upper (D 9) (R 9) [34,65,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7303 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7304 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 4, targets := 416 },{ cop := 2, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7),(2,8)], upper := (rows 35 67 69 140 304 440 472 408 408), lower := (rows 35 67 69 140 304 32 64 128 256), losses := [] }

theorem u7304 : Upper (D 9) (R 9) [34,65,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7304 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7305 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 4, targets := 416 },{ cop := 2, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7),(2,8)], upper := (rows 35 67 69 140 400 312 376 440 312), lower := (rows 35 67 69 140 400 32 64 128 256), losses := [] }

theorem u7305 : Upper (D 9) (R 9) [34,65,65,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7305 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7306 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 4, targets := 416 },{ cop := 2, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7),(2,8)], upper := (rows 35 67 69 152 280 420 484 420 420), lower := (rows 35 67 69 152 280 32 64 128 256), losses := [] }

theorem u7306 : Upper (D 9) (R 9) [34,65,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7306 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7307 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 4, targets := 416 },{ cop := 2, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7),(2,8)], upper := (rows 35 67 69 152 304 428 460 396 396), lower := (rows 35 67 69 152 304 32 64 128 256), losses := [] }

theorem u7307 : Upper (D 9) (R 9) [34,65,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7307 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7308 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 4, targets := 416 },{ cop := 2, region := 2, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7),(2,8)], upper := (rows 35 67 69 168 400 316 348 412 284), lower := (rows 35 67 69 168 400 32 64 128 256), losses := [] }

theorem u7308 : Upper (D 9) (R 9) [34,65,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7308 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7309 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 4, region := 355, targets := 128 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,6)], upper := (rows 35 67 76 137 148 304 368 432 304), lower := (rows 35 67 76 137 148 32 64 128 256), losses := [] }

theorem u7309 : Upper (D 9) (R 9) [34,65,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7309 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7310 : Route 9 := (fun mask => (mask,id))

def c7310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7310 : Upper (D 9) (R 9) [34,65,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,160] 13 (by decide) (choices 1) [4,16,256] r7310 c7310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4145
  · exact u4146
  · exact u4147

def r7311 : Route 9 := (fun mask => (mask,id))

def c7311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7311 : Upper (D 9) (R 9) [34,65,72,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,260] 13 (by decide) (choices 1) [16,128,256] r7311 c7311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4148
  · exact u4149
  · exact u4150

def r7312 : Route 9 := (fun mask => (mask,id))

def c7312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7312 : Upper (D 9) (R 9) [34,65,72,129,288] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,288] 13 (by decide) (choices 1) [4,16,128,256] r7312 c7312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4151
  · exact u4152
  · exact u4153
  · exact u4154

def r7313 : Route 9 := (fun mask => (mask,id))

def c7313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7313 : Upper (D 9) (R 9) [34,65,72,129,384] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,384] 13 (by decide) (choices 1) [4,16,256] r7313 c7313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4155
  · exact u4156
  · exact u4157

def b7314 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 364, targets := 1 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(2,0),(3,0),(4,6)], upper := (rows 35 67 76 140 145 304 368 432 304), lower := (rows 35 67 76 140 145 32 64 128 256), losses := [] }

theorem u7314 : Upper (D 9) (R 9) [34,65,72,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7314 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7315 : Route 9 := (fun mask => (mask,id))

def c7315 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7315 : Upper (D 9) (R 9) [34,65,72,132,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,132,160] 13 (by decide) (choices 1) [1,16,256] r7315 c7315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4158
  · exact u4159
  · exact u4160

def r7316 : Route 9 := (fun mask => (mask,id))

def c7316 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7316 : Upper (D 9) (R 9) [34,65,72,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,72,132,257] 13 (by decide) (choices 1) [16,128,256] r7316 c7316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4161
  · exact u4162
  · exact u4163

def r7317 : Route 9 := (fun mask => (mask,id))

def c7317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7317 : Upper (D 9) (R 9) [34,65,72,132,288] 13 := by
  apply FastRouting.sound _ _ [34,65,72,132,288] 13 (by decide) (choices 1) [1,16,128,256] r7317 c7317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4164
  · exact u4165
  · exact u4166
  · exact u4167

def r7318 : Route 9 := (fun mask => (mask,id))

def c7318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7318 : Upper (D 9) (R 9) [34,65,72,132,384] 13 := by
  apply FastRouting.sound _ _ [34,65,72,132,384] 13 (by decide) (choices 1) [1,16,256] r7318 c7318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4168
  · exact u4169
  · exact u4170

def b7319 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 96 }], pairs := [(0,7),(1,7),(2,7),(3,5),(3,6)], upper := (rows 35 67 76 152 145 292 356 420 292), lower := (rows 35 67 76 152 145 32 64 128 256), losses := [] }

theorem u7319 : Upper (D 9) (R 9) [34,65,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7319 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u7319
end Delivery.IrregularNine14.P09
