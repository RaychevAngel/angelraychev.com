import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0052
import IrregularNine14P07C0053

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r15360 : Route 9 := (fun mask => (mask,id))

def c15360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15360 : Upper (D 7) (R 7) [6,288,72,130,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,160,64] 13 (by decide) (choices 1) [1,16] r15360 c15360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3134
  · exact u3135

def r15361 : Route 9 := (fun mask => (mask,id))

def c15361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15361 : Upper (D 7) (R 7) [6,288,72,130,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,192,1] 13 (by decide) (choices 1) [1,16,32] r15361 c15361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3136
  · exact u3137
  · exact u3138

def r15362 : Route 9 := (fun mask => (mask,id))

def c15362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15362 : Upper (D 7) (R 7) [6,288,72,130,192,16] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,192,16] 13 (by decide) (choices 1) [1,32] r15362 c15362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3139
  · exact u3140

def b15363 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 7 290 76 152 49 33 194 194 450), lower := (rows 7 290 76 152 49 33 64 128 256), losses := [] }

theorem u15363 : Upper (D 7) (R 7) [6,288,72,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15364 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 204, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 290 76 152 49 34 193 193 449), lower := (rows 7 290 76 152 49 34 64 128 256), losses := [] }

theorem u15364 : Upper (D 7) (R 7) [6,288,72,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15365 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6),(2,5),(3,6),(4,1)], upper := (rows 7 290 76 152 49 96 195 131 387), lower := (rows 7 290 76 152 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 100 64 128 256), good := (rows 53 288 108 152 49 96 96 128 256) },{ target := 5, region := (rows 1 2 20 24 16 0 65 129 257), good := (rows 455 258 76 156 477 64 64 128 256) }] }

theorem u15365 : Upper (D 7) (R 7) [6,288,72,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15366 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 322, targets := 128 }], pairs := [(0,7),(1,7),(2,5),(3,5)], upper := (rows 7 290 76 152 49 160 67 195 323), lower := (rows 7 290 76 152 49 160 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 65 129 257), good := (rows 455 258 76 156 477 128 64 128 256) },{ target := 7, region := (rows 9 18 12 8 16 32 89 0 281), good := (rows 327 290 333 351 371 32 64 0 256) }] }

theorem u15366 : Upper (D 7) (R 7) [6,288,72,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15367 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 4, region := 426, targets := 64 },{ cop := 5, region := 386, targets := 1 }], pairs := [(0,6),(1,0),(1,6),(3,6)], upper := (rows 7 290 76 152 81 33 226 162 418), lower := (rows 7 290 76 152 81 33 64 128 256), losses := [] }

theorem u15367 : Upper (D 7) (R 7) [6,288,72,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15368 : PairBound 9 := { available := 161, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 7 290 76 152 81 34 225 161 417), lower := (rows 7 290 76 152 81 34 64 128 256), losses := [] }

theorem u15368 : Upper (D 7) (R 7) [6,288,72,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15369 : Route 9 := (fun mask => (mask,id))

def c15369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15369 : Upper (D 7) (R 7) [6,288,72,144,65,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,144,65,128] 13 (by decide) (choices 1) [1,2,32] r15369 c15369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3141
  · exact u3142
  · exact u3143

def r15370 : Route 9 := (fun mask => (mask,id))

def c15370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15370 : Upper (D 7) (R 7) [6,288,72,144,66,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,144,66,1] 13 (by decide) (choices 1) [1,32,128] r15370 c15370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3144
  · exact u3145
  · exact u3146

def r15371 : Route 9 := (fun mask => (mask,id))

def c15371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15371 : Upper (D 7) (R 7) [6,288,72,144,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,144,66,128] 13 (by decide) (choices 1) [1,32] r15371 c15371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3147
  · exact u3148

def r15372 : Route 9 := (fun mask => (mask,id))

def c15372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15372 : Upper (D 7) (R 7) [6,288,72,144,96,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,144,96,1] 13 (by decide) (choices 1) [1,2,128] r15372 c15372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3149
  · exact u3150
  · exact u3151

def b15373 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 7 290 76 152 112 34 193 129 385), lower := (rows 7 290 76 152 112 34 64 128 256), losses := [] }

theorem u15373 : Upper (D 7) (R 7) [6,288,72,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15374 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 7 290 76 152 112 160 67 131 259), lower := (rows 7 290 76 152 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 22 290 124 184 112 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 21 288 124 184 112 160 64 160 256) }] }

theorem u15374 : Upper (D 7) (R 7) [6,288,72,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15375 : Route 9 := (fun mask => (mask,id))

def c15375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15375 : Upper (D 7) (R 7) [6,288,72,160,65,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,65,1] 13 (by decide) (choices 1) [2,16,128] r15375 c15375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3152
  · exact u3153
  · exact u3154

def b15376 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 7 290 76 168 81 34 209 145 401), lower := (rows 7 290 76 168 81 34 64 128 256), losses := [] }

theorem u15376 : Upper (D 7) (R 7) [6,288,72,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15377 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,6),(3,6),(4,5)], upper := (rows 7 290 76 168 81 48 195 131 387), lower := (rows 7 290 76 168 81 48 64 128 256), losses := [] }

theorem u15377 : Upper (D 7) (R 7) [6,288,72,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15377 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15378 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 290 76 168 81 160 83 147 275), lower := (rows 7 290 76 168 81 160 64 128 256), losses := [] }

theorem u15378 : Upper (D 7) (R 7) [6,288,72,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15379 : Route 9 := (fun mask => (mask,id))

def c15379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15379 : Upper (D 7) (R 7) [6,288,72,160,66,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,66,1] 13 (by decide) (choices 1) [1,16,128] r15379 c15379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3155
  · exact u3156
  · exact u3157

def r15380 : Route 9 := (fun mask => (mask,id))

def c15380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15380 : Upper (D 7) (R 7) [6,288,72,160,66,16] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,66,16] 13 (by decide) (choices 1) [1,128] r15380 c15380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3158
  · exact u3159

def b15381 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 290 76 168 82 160 81 145 273), lower := (rows 7 290 76 168 82 160 64 128 256), losses := [] }

theorem u15381 : Upper (D 7) (R 7) [6,288,72,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15382 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 40, targets := 66 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,7),(3,1),(3,6),(4,5)], upper := (rows 7 290 76 168 145 33 82 210 338), lower := (rows 7 290 76 168 145 33 64 128 256), losses := [] }

theorem u15382 : Upper (D 7) (R 7) [6,288,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15383 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 7 290 76 168 145 34 81 209 337), lower := (rows 7 290 76 168 145 34 64 128 256), losses := [] }

theorem u15383 : Upper (D 7) (R 7) [6,288,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15384 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 76 168 145 48 67 195 323), lower := (rows 7 290 76 168 145 48 64 128 256), losses := [] }

theorem u15384 : Upper (D 7) (R 7) [6,288,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15384 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15385 : Route 9 := (fun mask => (mask,id))

def c15385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15385 : Upper (D 7) (R 7) [6,288,72,160,129,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,129,64] 13 (by decide) (choices 1) [1,2,16] r15385 c15385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3160
  · exact u3161
  · exact u3162

def r15386 : Route 9 := (fun mask => (mask,id))

def c15386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15386 : Upper (D 7) (R 7) [6,288,72,160,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,130,1] 13 (by decide) (choices 1) [1,16] r15386 c15386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3163
  · exact u3164

def b15387 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 76 168 146 48 65 193 321), lower := (rows 7 290 76 168 146 48 64 128 256), losses := [] }

theorem u15387 : Upper (D 7) (R 7) [6,288,72,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15387 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15388 : Route 9 := (fun mask => (mask,id))

def c15388 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15388 : Upper (D 7) (R 7) [6,288,72,160,130,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,130,64] 13 (by decide) (choices 1) [1,16] r15388 c15388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3165
  · exact u3166

def r15389 : Route 9 := (fun mask => (mask,id))

def c15389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15389 : Upper (D 7) (R 7) [6,288,72,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,192,1] 13 (by decide) (choices 1) [1,2,16] r15389 c15389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3167
  · exact u3168
  · exact u3169

def b15390 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 7 290 76 168 208 34 81 145 273), lower := (rows 7 290 76 168 208 34 64 128 256), losses := [] }

theorem u15390 : Upper (D 7) (R 7) [6,288,72,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15391 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 290 76 168 208 48 67 131 259), lower := (rows 7 290 76 168 208 48 64 128 256), losses := [] }

theorem u15391 : Upper (D 7) (R 7) [6,288,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15391 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15392 : Route 9 := (fun mask => (mask,id))

def c15392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15392 : Upper (D 7) (R 7) [6,288,96,17,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,96,17,130,1] 13 (by decide) (choices 1) [8,128] r15392 c15392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3170
  · exact u3171

def b15393 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 290 100 25 146 40 193 193 449), lower := (rows 7 290 100 25 146 40 64 128 256), losses := [] }

theorem u15393 : Upper (D 7) (R 7) [6,288,96,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15393 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15394 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 290 100 25 146 96 201 137 393), lower := (rows 7 290 100 25 146 96 64 128 256), losses := [] }

theorem u15394 : Upper (D 7) (R 7) [6,288,96,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15395 : Route 9 := (fun mask => (mask,id))

def c15395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15395 : Upper (D 7) (R 7) [6,288,96,17,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,96,17,130,128] 13 (by decide) (choices 1) [1,8] r15395 c15395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3172
  · exact u3173

def b15396 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 7 290 100 25 152 33 194 194 450), lower := (rows 7 290 100 25 152 33 64 128 256), losses := [] }

theorem u15396 : Upper (D 7) (R 7) [6,288,96,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15397 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 100 25 152 34 193 193 449), lower := (rows 7 290 100 25 152 34 64 128 256), losses := [] }

theorem u15397 : Upper (D 7) (R 7) [6,288,96,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15398 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 290 100 25 152 96 195 131 387), lower := (rows 7 290 100 25 152 96 64 128 256), losses := [] }

theorem u15398 : Upper (D 7) (R 7) [6,288,96,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15399 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 290 100 25 152 160 67 195 323), lower := (rows 7 290 100 25 152 160 64 128 256), losses := [] }

theorem u15399 : Upper (D 7) (R 7) [6,288,96,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15400 : Route 9 := (fun mask => (mask,id))

def c15400 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15400 : Upper (D 7) (R 7) [6,288,96,17,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,96,17,192,1] 13 (by decide) (choices 1) [2,8,128] r15400 c15400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3174
  · exact u3175
  · exact u3176

def b15401 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 100 25 208 34 201 137 393), lower := (rows 7 290 100 25 208 34 64 128 256), losses := [] }

theorem u15401 : Upper (D 7) (R 7) [6,288,96,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15402 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 290 100 25 208 40 195 131 387), lower := (rows 7 290 100 25 208 40 64 128 256), losses := [] }

theorem u15402 : Upper (D 7) (R 7) [6,288,96,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15402 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15403 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 7 290 100 25 208 160 75 139 267), lower := (rows 7 290 100 25 208 160 64 128 256), losses := [] }

theorem u15403 : Upper (D 7) (R 7) [6,288,96,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15404 : Route 9 := (fun mask => (mask,id))

def c15404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15404 : Upper (D 7) (R 7) [6,288,96,18,129,1] 13 := by
  apply FastRouting.sound _ _ [6,288,96,18,129,1] 13 (by decide) (choices 1) [8,128] r15404 c15404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3177
  · exact u3178

def b15405 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 290 100 26 145 40 193 193 449), lower := (rows 7 290 100 26 145 40 64 128 256), losses := [] }

theorem u15405 : Upper (D 7) (R 7) [6,288,96,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15405 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15406 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 290 100 26 145 96 201 137 393), lower := (rows 7 290 100 26 145 96 64 128 256), losses := [] }

theorem u15406 : Upper (D 7) (R 7) [6,288,96,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15407 : Route 9 := (fun mask => (mask,id))

def c15407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15407 : Upper (D 7) (R 7) [6,288,96,18,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,96,18,129,128] 13 (by decide) (choices 1) [1,8] r15407 c15407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3179
  · exact u3180

def r15408 : Route 9 := (fun mask => (mask,id))

def c15408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15408 : Upper (D 7) (R 7) [6,288,96,18,136,1] 13 := by
  apply FastRouting.sound _ _ [6,288,96,18,136,1] 13 (by decide) (choices 1) [1,128] r15408 c15408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3181
  · exact u3182

def b15409 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 290 100 26 152 96 193 129 385), lower := (rows 7 290 100 26 152 96 64 128 256), losses := [] }

theorem u15409 : Upper (D 7) (R 7) [6,288,96,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15410 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 290 100 26 152 160 65 193 321), lower := (rows 7 290 100 26 152 160 64 128 256), losses := [] }

theorem u15410 : Upper (D 7) (R 7) [6,288,96,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15411 : Route 9 := (fun mask => (mask,id))

def c15411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15411 : Upper (D 7) (R 7) [6,288,96,18,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,96,18,192,1] 13 (by decide) (choices 1) [1,8,128] r15411 c15411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3183
  · exact u3184
  · exact u3185

def b15412 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 290 100 26 208 40 193 129 385), lower := (rows 7 290 100 26 208 40 64 128 256), losses := [] }

theorem u15412 : Upper (D 7) (R 7) [6,288,96,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15412 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15413 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 7 290 100 26 208 160 73 137 265), lower := (rows 7 290 100 26 208 160 64 128 256), losses := [] }

theorem u15413 : Upper (D 7) (R 7) [6,288,96,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15414 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 290 100 74 145 33 216 152 408), lower := (rows 7 290 100 74 145 33 64 128 256), losses := [] }

theorem u15414 : Upper (D 7) (R 7) [6,288,96,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15415 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 290 100 74 145 40 209 145 401), lower := (rows 7 290 100 74 145 40 64 128 256), losses := [] }

theorem u15415 : Upper (D 7) (R 7) [6,288,96,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15415 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15416 : Route 9 := (fun mask => (mask,id))

def c15416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15416 : Upper (D 7) (R 7) [6,288,96,66,129,16] 13 := by
  apply FastRouting.sound _ _ [6,288,96,66,129,16] 13 (by decide) (choices 1) [1,8,128] r15416 c15416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3186
  · exact u3187
  · exact u3188

def r15417 : Route 9 := (fun mask => (mask,id))

def c15417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15417 : Upper (D 7) (R 7) [6,288,96,66,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,96,66,129,128] 13 (by decide) (choices 1) [1,8,16] r15417 c15417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3189
  · exact u3190
  · exact u3191

def b15418 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 290 100 74 152 33 209 145 401), lower := (rows 7 290 100 74 152 33 64 128 256), losses := [] }

theorem u15418 : Upper (D 7) (R 7) [6,288,96,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15419 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 290 100 74 152 48 193 129 385), lower := (rows 7 290 100 74 152 48 64 128 256), losses := [] }

theorem u15419 : Upper (D 7) (R 7) [6,288,96,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15419 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15419
end Delivery.IrregularNine14.P07
