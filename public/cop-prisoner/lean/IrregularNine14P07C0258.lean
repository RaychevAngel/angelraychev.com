import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0054
import IrregularNine14P07C0055

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15480 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 290 196 56 82 40 193 129 385), lower := (rows 7 290 196 56 82 40 64 128 256), losses := [] }

theorem u15480 : Upper (D 7) (R 7) [6,288,192,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15480 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15481 : Route 9 := (fun mask => (mask,id))

def c15481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15481 : Upper (D 7) (R 7) [6,288,192,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,192,48,66,128] 13 (by decide) (choices 1) [1,8] r15481 c15481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3248
  · exact u3249

def r15482 : Route 9 := (fun mask => (mask,id))

def c15482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15482 : Upper (D 7) (R 7) [6,288,192,65,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,130,1] 13 (by decide) (choices 1) [8,16,32] r15482 c15482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3250
  · exact u3251
  · exact u3252

def r15483 : Route 9 := (fun mask => (mask,id))

def c15483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15483 : Upper (D 7) (R 7) [6,288,192,65,130,8] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,130,8] 13 (by decide) (choices 1) [1,16,32] r15483 c15483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3253
  · exact u3254
  · exact u3255

def r15484 : Route 9 := (fun mask => (mask,id))

def c15484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15484 : Upper (D 7) (R 7) [6,288,192,65,130,16] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,130,16] 13 (by decide) (choices 1) [1,8,32] r15484 c15484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3256
  · exact u3257
  · exact u3258

def r15485 : Route 9 := (fun mask => (mask,id))

def c15485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15485 : Upper (D 7) (R 7) [6,288,192,65,136,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,136,1] 13 (by decide) (choices 1) [2,16,32] r15485 c15485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3259
  · exact u3260
  · exact u3261

def b15486 : PairBound 9 := { available := 49, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 290 196 73 152 34 113 177 305), lower := (rows 7 290 196 73 152 34 64 128 256), losses := [] }

theorem u15486 : Upper (D 7) (R 7) [6,288,192,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15487 : Route 9 := (fun mask => (mask,id))

def c15487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15487 : Upper (D 7) (R 7) [6,288,192,65,136,16] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,136,16] 13 (by decide) (choices 1) [1,2,32] r15487 c15487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3262
  · exact u3263
  · exact u3264

def r15488 : Route 9 := (fun mask => (mask,id))

def c15488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15488 : Upper (D 7) (R 7) [6,288,192,65,160,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,160,1] 13 (by decide) (choices 1) [2,8,16] r15488 c15488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3265
  · exact u3266
  · exact u3267

def b15489 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 290 196 73 176 34 89 153 281), lower := (rows 7 290 196 73 176 34 64 128 256), losses := [] }

theorem u15489 : Upper (D 7) (R 7) [6,288,192,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15490 : Route 9 := (fun mask => (mask,id))

def c15490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15490 : Upper (D 7) (R 7) [6,288,192,65,160,8] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,160,8] 13 (by decide) (choices 1) [1,2,16] r15490 c15490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3268
  · exact u3269
  · exact u3270

def b15491 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 196 73 176 48 75 139 267), lower := (rows 7 290 196 73 176 48 64 128 256), losses := [] }

theorem u15491 : Upper (D 7) (R 7) [6,288,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15491 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15492 : Route 9 := (fun mask => (mask,id))

def c15492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15492 : Upper (D 7) (R 7) [6,288,192,66,136,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,66,136,1] 13 (by decide) (choices 1) [1,16,32] r15492 c15492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3271
  · exact u3272
  · exact u3273

def r15493 : Route 9 := (fun mask => (mask,id))

def c15493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15493 : Upper (D 7) (R 7) [6,288,192,66,136,16] 13 := by
  apply FastRouting.sound _ _ [6,288,192,66,136,16] 13 (by decide) (choices 1) [1,32] r15493 c15493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3274
  · exact u3275

def r15494 : Route 9 := (fun mask => (mask,id))

def c15494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15494 : Upper (D 7) (R 7) [6,288,192,66,160,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,66,160,1] 13 (by decide) (choices 1) [1,8,16] r15494 c15494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3276
  · exact u3277
  · exact u3278

def r15495 : Route 9 := (fun mask => (mask,id))

def c15495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15495 : Upper (D 7) (R 7) [6,288,192,66,160,8] 13 := by
  apply FastRouting.sound _ _ [6,288,192,66,160,8] 13 (by decide) (choices 1) [1,16] r15495 c15495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3279
  · exact u3280

def b15496 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 196 74 176 48 73 137 265), lower := (rows 7 290 196 74 176 48 64 128 256), losses := [] }

theorem u15496 : Upper (D 7) (R 7) [6,288,192,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15496 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15497 : Route 9 := (fun mask => (mask,id))

def c15497 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15497 : Upper (D 7) (R 7) [6,288,192,80,160,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,80,160,1] 13 (by decide) (choices 1) [1,2,8] r15497 c15497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3281
  · exact u3282
  · exact u3283

def r15498 : Route 9 := (fun mask => (mask,id))

def c15498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15498 : Upper (D 7) (R 7) [6,288,192,80,160,2] 13 := by
  apply FastRouting.sound _ _ [6,288,192,80,160,2] 13 (by decide) (choices 1) [1,8] r15498 c15498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3284
  · exact u3285

def b15499 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 290 196 88 176 40 67 131 259), lower := (rows 7 290 196 88 176 40 64 128 256), losses := [] }

theorem u15499 : Upper (D 7) (R 7) [6,288,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15499 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15500 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 21 74 146 96 480 416 416), lower := (rows 13 35 21 74 146 96 64 128 256), losses := [] }

theorem u15500 : Upper (D 7) (R 7) [12,33,17,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15501 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(3,0),(3,7),(4,0)], upper := (rows 13 35 21 74 146 160 352 480 352), lower := (rows 13 35 21 74 146 160 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 176 0 128 256), good := (rows 15 35 55 10 178 160 0 160 256) }] }

theorem u15501 : Upper (D 7) (R 7) [12,33,17,66,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15502 : Route 9 := (fun mask => (mask,id))

def c15502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15502 : Upper (D 7) (R 7) [12,33,17,66,130,256] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,130,256] 13 (by decide) (choices 1) [32,128] r15502 c15502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3286
  · exact u3287

def b15503 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 74 176 34 448 448 448), lower := (rows 13 35 21 74 176 34 64 128 256), losses := [] }

theorem u15503 : Upper (D 7) (R 7) [12,33,17,66,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15504 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 21 74 176 96 450 386 386), lower := (rows 13 35 21 74 176 96 64 128 256), losses := [] }

theorem u15504 : Upper (D 7) (R 7) [12,33,17,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15505 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 21 74 176 160 322 450 322), lower := (rows 13 35 21 74 176 160 64 128 256), losses := [] }

theorem u15505 : Upper (D 7) (R 7) [12,33,17,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15506 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 216, targets := 1 },{ cop := 1, region := 200, targets := 32 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 13 35 21 74 176 288 194 194 450), lower := (rows 13 35 21 74 176 288 64 128 256), losses := [] }

theorem u15506 : Upper (D 7) (R 7) [12,33,17,66,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15506 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15507 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 21 74 208 34 480 416 416), lower := (rows 13 35 21 74 208 34 64 128 256), losses := [] }

theorem u15507 : Upper (D 7) (R 7) [12,33,17,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15508 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 418, targets := 64 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(3,0),(3,7),(4,0)], upper := (rows 13 35 21 74 208 160 354 418 290), lower := (rows 13 35 21 74 208 160 64 128 256), losses := [] }

theorem u15508 : Upper (D 7) (R 7) [12,33,17,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15509 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 216, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 13 35 21 74 208 288 226 162 418), lower := (rows 13 35 21 74 208 288 64 128 256), losses := [] }

theorem u15509 : Upper (D 7) (R 7) [12,33,17,66,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15509 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15510 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 21 74 274 96 224 160 416), lower := (rows 13 35 21 74 274 96 64 128 256), losses := [] }

theorem u15510 : Upper (D 7) (R 7) [12,33,17,66,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15511 : Route 9 := (fun mask => (mask,id))

def c15511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15511 : Upper (D 7) (R 7) [12,33,17,66,258,128] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,258,128] 13 (by decide) (choices 1) [32,128] r15511 c15511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3288
  · exact u3289

def b15512 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 74 304 34 192 192 448), lower := (rows 13 35 21 74 304 34 64 128 256), losses := [] }

theorem u15512 : Upper (D 7) (R 7) [12,33,17,66,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15513 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 21 74 304 96 194 130 386), lower := (rows 13 35 21 74 304 96 64 128 256), losses := [] }

theorem u15513 : Upper (D 7) (R 7) [12,33,17,66,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15514 : Route 9 := (fun mask => (mask,id))

def c15514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15514 : Upper (D 7) (R 7) [12,33,17,66,288,128] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,288,128] 13 (by decide) (choices 1) [2,128] r15514 c15514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3290
  · exact u3291

def b15515 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 21 74 336 34 224 160 416), lower := (rows 13 35 21 74 336 34 64 128 256), losses := [] }

theorem u15515 : Upper (D 7) (R 7) [12,33,17,66,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15516 : Route 9 := (fun mask => (mask,id))

def c15516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15516 : Upper (D 7) (R 7) [12,33,17,66,320,128] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,320,128] 13 (by decide) (choices 1) [2,32,128] r15516 c15516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3292
  · exact u3293
  · exact u3294

def b15517 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 74 400 34 224 224 480), lower := (rows 13 35 21 74 400 34 64 128 256), losses := [] }

theorem u15517 : Upper (D 7) (R 7) [12,33,17,66,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15518 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 21 74 400 96 226 162 418), lower := (rows 13 35 21 74 400 96 64 128 256), losses := [] }

theorem u15518 : Upper (D 7) (R 7) [12,33,17,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15519 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 72, targets := 128 }], pairs := [(1,6),(3,0),(3,7),(4,0)], upper := (rows 13 35 21 74 400 160 98 226 354), lower := (rows 13 35 21 74 400 160 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 176 0 128 256), good := (rows 15 35 55 10 432 160 0 160 256) }] }

theorem u15519 : Upper (D 7) (R 7) [12,33,17,66,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15520 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 21 200 82 34 480 416 416), lower := (rows 13 35 21 200 82 34 64 128 256), losses := [] }

theorem u15520 : Upper (D 7) (R 7) [12,33,17,192,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15521 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 21 200 82 160 354 418 290), lower := (rows 13 35 21 200 82 160 64 128 256), losses := [] }

theorem u15521 : Upper (D 7) (R 7) [12,33,17,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15522 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 216, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 13 35 21 200 82 288 226 162 418), lower := (rows 13 35 21 200 82 288 64 128 256), losses := [] }

theorem u15522 : Upper (D 7) (R 7) [12,33,17,192,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15522 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15523 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 200 274 34 224 224 480), lower := (rows 13 35 21 200 274 34 64 128 256), losses := [] }

theorem u15523 : Upper (D 7) (R 7) [12,33,17,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15524 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 21 200 274 96 226 162 418), lower := (rows 13 35 21 200 274 96 64 128 256), losses := [] }

theorem u15524 : Upper (D 7) (R 7) [12,33,17,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15525 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 200 304 34 194 194 450), lower := (rows 13 35 21 200 304 34 64 128 256), losses := [] }

theorem u15525 : Upper (D 7) (R 7) [12,33,17,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15526 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 21 200 304 96 194 130 386), lower := (rows 13 35 21 200 304 96 64 128 256), losses := [] }

theorem u15526 : Upper (D 7) (R 7) [12,33,17,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15527 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 200 336 34 226 162 418), lower := (rows 13 35 21 200 336 34 64 128 256), losses := [] }

theorem u15527 : Upper (D 7) (R 7) [12,33,17,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15528 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 21 200 336 160 98 162 290), lower := (rows 13 35 21 200 336 160 64 128 256), losses := [] }

theorem u15528 : Upper (D 7) (R 7) [12,33,17,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15529 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(0,6),(3,0),(3,6),(4,0)], upper := (rows 13 35 21 266 82 96 224 160 416), lower := (rows 13 35 21 266 82 96 64 128 256), losses := [{ target := 6, region := (rows 21 2 20 26 16 32 0 162 290), good := (rows 13 427 29 394 415 416 0 128 256) }] }

theorem u15529 : Upper (D 7) (R 7) [12,33,17,258,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15530 : Route 9 := (fun mask => (mask,id))

def c15530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15530 : Upper (D 7) (R 7) [12,33,17,258,66,128] 13 := by
  apply FastRouting.sound _ _ [12,33,17,258,66,128] 13 (by decide) (choices 1) [32,128] r15530 c15530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3295
  · exact u3296

def b15531 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 266 112 34 192 192 448), lower := (rows 13 35 21 266 112 34 64 128 256), losses := [] }

theorem u15531 : Upper (D 7) (R 7) [12,33,17,258,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15532 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 13 35 21 266 112 96 194 130 386), lower := (rows 13 35 21 266 112 96 64 128 256), losses := [] }

theorem u15532 : Upper (D 7) (R 7) [12,33,17,258,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15533 : Route 9 := (fun mask => (mask,id))

def c15533 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15533 : Upper (D 7) (R 7) [12,33,17,258,96,128] 13 := by
  apply FastRouting.sound _ _ [12,33,17,258,96,128] 13 (by decide) (choices 1) [2,128] r15533 c15533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3297
  · exact u3298

def b15534 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 266 208 34 224 224 480), lower := (rows 13 35 21 266 208 34 64 128 256), losses := [] }

theorem u15534 : Upper (D 7) (R 7) [12,33,17,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15535 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(1,7),(3,0),(3,6),(4,0)], upper := (rows 13 35 21 266 208 96 226 162 418), lower := (rows 13 35 21 266 208 96 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 112 64 0 256), good := (rows 15 35 55 266 112 96 96 0 256) }] }

theorem u15535 : Upper (D 7) (R 7) [12,33,17,258,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15536 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 21 328 82 34 224 160 416), lower := (rows 13 35 21 328 82 34 64 128 256), losses := [] }

theorem u15536 : Upper (D 7) (R 7) [12,33,17,320,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15537 : Route 9 := (fun mask => (mask,id))

def c15537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15537 : Upper (D 7) (R 7) [12,33,17,320,66,128] 13 := by
  apply FastRouting.sound _ _ [12,33,17,320,66,128] 13 (by decide) (choices 1) [2,32,128] r15537 c15537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3299
  · exact u3300
  · exact u3301

def b15538 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 21 328 146 34 224 224 480), lower := (rows 13 35 21 328 146 34 64 128 256), losses := [] }

theorem u15538 : Upper (D 7) (R 7) [12,33,17,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15539 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 148, targets := 64 }], pairs := [(2,6),(3,0),(4,0),(4,6)], upper := (rows 13 35 21 328 146 96 226 162 418), lower := (rows 13 35 21 328 146 96 64 128 256), losses := [] }

theorem u15539 : Upper (D 7) (R 7) [12,33,17,320,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15539
end Delivery.IrregularNine14.P07
