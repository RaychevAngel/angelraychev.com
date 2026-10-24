import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0186
import IrregularNine14P07C0187

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29340 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 97 262 164 25 146 40 67 195 323), lower := (rows 97 262 164 25 146 40 64 128 256), losses := [] }

theorem u29340 : Upper (D 7) (R 7) [96,260,160,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29340 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29341 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 164 25 146 96 75 139 267), lower := (rows 97 262 164 25 146 96 64 128 256), losses := [] }

theorem u29341 : Upper (D 7) (R 7) [96,260,160,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29342 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 97 262 164 25 152 33 66 194 322), lower := (rows 97 262 164 25 152 33 64 128 256), losses := [] }

theorem u29342 : Upper (D 7) (R 7) [96,260,160,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29343 : Route 9 := (fun mask => (mask,id))

def c29343 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29343 : Upper (D 7) (R 7) [96,260,160,17,136,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,136,2] 13 (by decide) (choices 1) [1,2] r29343 c29343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11191
  · exact u11192

def b29344 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 164 25 152 96 67 131 259), lower := (rows 97 262 164 25 152 96 64 128 256), losses := [] }

theorem u29344 : Upper (D 7) (R 7) [96,260,160,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29345 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 3, region := 422, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(3,1)], upper := (rows 97 262 164 25 208 33 74 138 266), lower := (rows 97 262 164 25 208 33 64 128 256), losses := [] }

theorem u29345 : Upper (D 7) (R 7) [96,260,160,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29346 : Route 9 := (fun mask => (mask,id))

def c29346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29346 : Upper (D 7) (R 7) [96,260,160,17,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,192,2] 13 (by decide) (choices 1) [1,2,8] r29346 c29346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11193
  · exact u11194
  · exact u11195

def b29347 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 262 164 25 208 40 67 131 259), lower := (rows 97 262 164 25 208 40 64 128 256), losses := [] }

theorem u29347 : Upper (D 7) (R 7) [96,260,160,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29347 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29348 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(2,6)], upper := (rows 97 262 164 26 88 33 195 131 387), lower := (rows 97 262 164 26 88 33 64 128 256), losses := [] }

theorem u29348 : Upper (D 7) (R 7) [96,260,160,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29349 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(2,6)], upper := (rows 97 262 164 26 88 34 193 129 385), lower := (rows 97 262 164 26 88 34 64 128 256), losses := [] }

theorem u29349 : Upper (D 7) (R 7) [96,260,160,18,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29350 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 97 262 164 26 88 160 67 131 259), lower := (rows 97 262 164 26 88 160 64 128 256), losses := [] }

theorem u29350 : Upper (D 7) (R 7) [96,260,160,18,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29351 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 36, targets := 66 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,6)], upper := (rows 97 262 164 26 145 33 74 202 330), lower := (rows 97 262 164 26 145 33 64 128 256), losses := [] }

theorem u29351 : Upper (D 7) (R 7) [96,260,160,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29352 : Route 9 := (fun mask => (mask,id))

def c29352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29352 : Upper (D 7) (R 7) [96,260,160,18,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,129,2] 13 (by decide) (choices 1) [1,8] r29352 c29352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11196
  · exact u11197

def r29353 : Route 9 := (fun mask => (mask,id))

def c29353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29353 : Upper (D 7) (R 7) [96,260,160,18,129,8] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,129,8] 13 (by decide) (choices 1) [1,2] r29353 c29353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11198
  · exact u11199

def b29354 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 164 26 145 96 75 139 267), lower := (rows 97 262 164 26 145 96 64 128 256), losses := [] }

theorem u29354 : Upper (D 7) (R 7) [96,260,160,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29355 : Route 9 := (fun mask => (mask,id))

def c29355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29355 : Upper (D 7) (R 7) [96,260,160,18,136,1] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,136,1] 13 (by decide) (choices 1) [1,2] r29355 c29355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11200
  · exact u11201

def b29356 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 97 262 164 26 152 34 65 193 321), lower := (rows 97 262 164 26 152 34 64 128 256), losses := [] }

theorem u29356 : Upper (D 7) (R 7) [96,260,160,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29357 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 164 26 152 96 67 131 259), lower := (rows 97 262 164 26 152 96 64 128 256), losses := [] }

theorem u29357 : Upper (D 7) (R 7) [96,260,160,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29358 : Route 9 := (fun mask => (mask,id))

def c29358 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29358 : Upper (D 7) (R 7) [96,260,160,18,192,1] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,192,1] 13 (by decide) (choices 1) [1,2,8] r29358 c29358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11202
  · exact u11203
  · exact u11204

def r29359 : Route 9 := (fun mask => (mask,id))

def c29359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29359 : Upper (D 7) (R 7) [96,260,160,18,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,192,2] 13 (by decide) (choices 1) [1,8] r29359 c29359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11205
  · exact u11206

def b29360 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,6),(2,6)], upper := (rows 97 262 164 26 208 40 67 131 259), lower := (rows 97 262 164 26 208 40 64 128 256), losses := [] }

theorem u29360 : Upper (D 7) (R 7) [96,260,160,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29360 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29361 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 33, targets := 130 },{ cop := 4, region := 36, targets := 66 }], pairs := [(0,1),(0,7),(2,1),(2,6)], upper := (rows 97 262 164 74 145 33 90 154 282), lower := (rows 97 262 164 74 145 33 64 128 256), losses := [] }

theorem u29361 : Upper (D 7) (R 7) [96,260,160,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29362 : Route 9 := (fun mask => (mask,id))

def c29362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29362 : Upper (D 7) (R 7) [96,260,160,66,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,66,129,2] 13 (by decide) (choices 1) [1,8,16] r29362 c29362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11207
  · exact u11208
  · exact u11209

def b29363 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 164 74 145 40 83 147 275), lower := (rows 97 262 164 74 145 40 64 128 256), losses := [] }

theorem u29363 : Upper (D 7) (R 7) [96,260,160,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29363 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29364 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 97 262 164 74 145 48 75 139 267), lower := (rows 97 262 164 74 145 48 64 128 256), losses := [] }

theorem u29364 : Upper (D 7) (R 7) [96,260,160,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29364 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29365 : Route 9 := (fun mask => (mask,id))

def c29365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29365 : Upper (D 7) (R 7) [96,260,160,66,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,160,66,130,1] 13 (by decide) (choices 1) [1,8,16] r29365 c29365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11210
  · exact u11211
  · exact u11212

def b29366 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 164 74 146 40 81 145 273), lower := (rows 97 262 164 74 146 40 64 128 256), losses := [] }

theorem u29366 : Upper (D 7) (R 7) [96,260,160,66,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29366 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29367 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 97 262 164 74 146 48 73 137 265), lower := (rows 97 262 164 74 146 48 64 128 256), losses := [] }

theorem u29367 : Upper (D 7) (R 7) [96,260,160,66,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29367 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29368 : Route 9 := (fun mask => (mask,id))

def c29368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29368 : Upper (D 7) (R 7) [96,260,160,66,136,1] 13 := by
  apply FastRouting.sound _ _ [96,260,160,66,136,1] 13 (by decide) (choices 1) [1,2,16] r29368 c29368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11213
  · exact u11214
  · exact u11215

def r29369 : Route 9 := (fun mask => (mask,id))

def c29369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29369 : Upper (D 7) (R 7) [96,260,160,66,136,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,66,136,2] 13 (by decide) (choices 1) [1,16] r29369 c29369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11216
  · exact u11217

def b29370 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 97 262 164 74 152 48 67 131 259), lower := (rows 97 262 164 74 152 48 64 128 256), losses := [] }

theorem u29370 : Upper (D 7) (R 7) [96,260,160,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29370 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29371 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 33, targets := 130 },{ cop := 4, region := 36, targets := 66 }], pairs := [(0,1),(0,7),(2,1),(2,6)], upper := (rows 97 262 164 88 145 33 74 138 266), lower := (rows 97 262 164 88 145 33 64 128 256), losses := [] }

theorem u29371 : Upper (D 7) (R 7) [96,260,160,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29372 : Route 9 := (fun mask => (mask,id))

def c29372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29372 : Upper (D 7) (R 7) [96,260,160,80,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,160,80,129,2] 13 (by decide) (choices 1) [1,2,8] r29372 c29372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11218
  · exact u11219
  · exact u11220

def b29373 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 164 88 145 40 67 131 259), lower := (rows 97 262 164 88 145 40 64 128 256), losses := [] }

theorem u29373 : Upper (D 7) (R 7) [96,260,160,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29373 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29374 : Route 9 := (fun mask => (mask,id))

def c29374 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29374 : Upper (D 7) (R 7) [96,260,160,80,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,160,80,130,1] 13 (by decide) (choices 1) [1,2,8] r29374 c29374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11221
  · exact u11222
  · exact u11223

def b29375 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 36, targets := 65 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,7)], upper := (rows 97 262 164 88 146 34 73 137 265), lower := (rows 97 262 164 88 146 34 64 128 256), losses := [] }

theorem u29375 : Upper (D 7) (R 7) [96,260,160,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29376 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 164 88 146 40 67 131 259), lower := (rows 97 262 164 88 146 40 64 128 256), losses := [] }

theorem u29376 : Upper (D 7) (R 7) [96,260,160,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29376 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29377 : Route 9 := (fun mask => (mask,id))

def c29377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29377 : Upper (D 7) (R 7) [96,288,3,17,130,4] 13 := by
  apply FastRouting.sound _ _ [96,288,3,17,130,4] 13 (by decide) (choices 1) [8,128] r29377 c29377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11224
  · exact u11225

def b29378 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 208, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 97 290 7 25 146 40 196 196 452), lower := (rows 97 290 7 25 146 40 64 128 256), losses := [] }

theorem u29378 : Upper (D 7) (R 7) [96,288,3,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29378 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29379 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 25 146 96 204 140 396), lower := (rows 97 290 7 25 146 96 64 128 256), losses := [] }

theorem u29379 : Upper (D 7) (R 7) [96,288,3,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29380 : Route 9 := (fun mask => (mask,id))

def c29380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29380 : Upper (D 7) (R 7) [96,288,3,17,130,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,17,130,128] 13 (by decide) (choices 1) [4,8] r29380 c29380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11226
  · exact u11227

def b29381 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 25 148 34 200 200 456), lower := (rows 97 290 7 25 148 34 64 128 256), losses := [] }

theorem u29381 : Upper (D 7) (R 7) [96,288,3,17,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29382 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 0, region := 386, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 97 290 7 25 148 40 194 194 450), lower := (rows 97 290 7 25 148 40 64 128 256), losses := [] }

theorem u29382 : Upper (D 7) (R 7) [96,288,3,17,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29382 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29383 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 25 148 96 202 138 394), lower := (rows 97 290 7 25 148 96 64 128 256), losses := [] }

theorem u29383 : Upper (D 7) (R 7) [96,288,3,17,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29384 : Route 9 := (fun mask => (mask,id))

def c29384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29384 : Upper (D 7) (R 7) [96,288,3,17,132,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,17,132,128] 13 (by decide) (choices 1) [2,8] r29384 c29384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11228
  · exact u11229

def b29385 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 25 152 34 196 196 452), lower := (rows 97 290 7 25 152 34 64 128 256), losses := [] }

theorem u29385 : Upper (D 7) (R 7) [96,288,3,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29386 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 0, region := 386, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 97 290 7 25 152 36 194 194 450), lower := (rows 97 290 7 25 152 36 64 128 256), losses := [] }

theorem u29386 : Upper (D 7) (R 7) [96,288,3,17,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29386 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29387 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 25 152 96 198 134 390), lower := (rows 97 290 7 25 152 96 64 128 256), losses := [] }

theorem u29387 : Upper (D 7) (R 7) [96,288,3,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29388 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 97 290 7 25 152 160 70 198 326), lower := (rows 97 290 7 25 152 160 64 128 256), losses := [] }

theorem u29388 : Upper (D 7) (R 7) [96,288,3,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29389 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 26 84 33 200 136 392), lower := (rows 97 290 7 26 84 33 64 128 256), losses := [] }

theorem u29389 : Upper (D 7) (R 7) [96,288,3,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29390 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,6),(2,6),(3,5)], upper := (rows 97 290 7 26 84 40 193 129 385), lower := (rows 97 290 7 26 84 40 64 128 256), losses := [] }

theorem u29390 : Upper (D 7) (R 7) [96,288,3,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29390 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29391 : Route 9 := (fun mask => (mask,id))

def c29391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29391 : Upper (D 7) (R 7) [96,288,3,18,68,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,68,128] 13 (by decide) (choices 1) [1,8,128] r29391 c29391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11230
  · exact u11231
  · exact u11232

def r29392 : Route 9 := (fun mask => (mask,id))

def c29392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29392 : Upper (D 7) (R 7) [96,288,3,18,129,4] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,129,4] 13 (by decide) (choices 1) [8,128] r29392 c29392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11233
  · exact u11234

def b29393 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 97 290 7 26 145 40 196 196 452), lower := (rows 97 290 7 26 145 40 64 128 256), losses := [] }

theorem u29393 : Upper (D 7) (R 7) [96,288,3,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29393 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29394 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 26 145 96 204 140 396), lower := (rows 97 290 7 26 145 96 64 128 256), losses := [] }

theorem u29394 : Upper (D 7) (R 7) [96,288,3,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29395 : Route 9 := (fun mask => (mask,id))

def c29395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29395 : Upper (D 7) (R 7) [96,288,3,18,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,129,128] 13 (by decide) (choices 1) [4,8] r29395 c29395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11235
  · exact u11236

def b29396 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 26 148 33 200 200 456), lower := (rows 97 290 7 26 148 33 64 128 256), losses := [] }

theorem u29396 : Upper (D 7) (R 7) [96,288,3,18,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29397 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(3,5),(4,5)], upper := (rows 97 290 7 26 148 40 193 193 449), lower := (rows 97 290 7 26 148 40 64 128 256), losses := [] }

theorem u29397 : Upper (D 7) (R 7) [96,288,3,18,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29397 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29398 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 26 148 96 201 137 393), lower := (rows 97 290 7 26 148 96 64 128 256), losses := [] }

theorem u29398 : Upper (D 7) (R 7) [96,288,3,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29399 : Route 9 := (fun mask => (mask,id))

def c29399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29399 : Upper (D 7) (R 7) [96,288,3,18,132,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,132,128] 13 (by decide) (choices 1) [1,8] r29399 c29399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11237
  · exact u11238

#print axioms u29399
end Delivery.IrregularNine14.P07
