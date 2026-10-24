import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0053
import IrregularNine14P07C0054

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r15420 : Route 9 := (fun mask => (mask,id))

def c15420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15420 : Upper (D 7) (R 7) [6,288,96,66,136,128] 13 := by
  apply FastRouting.sound _ _ [6,288,96,66,136,128] 13 (by decide) (choices 1) [1,16] r15420 c15420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3192
  · exact u3193

def b15421 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(1,6),(2,1),(3,5),(4,5)], upper := (rows 7 290 100 88 145 33 202 138 394), lower := (rows 7 290 100 88 145 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 64 128 256), good := (rows 37 288 100 124 177 33 64 128 256) },{ target := 6, region := (rows 1 10 4 8 16 49 0 136 264), good := (rows 39 290 36 442 177 33 0 128 256) }] }

theorem u15421 : Upper (D 7) (R 7) [6,288,96,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15422 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 100 88 145 34 201 137 393), lower := (rows 7 290 100 88 145 34 64 128 256), losses := [] }

theorem u15422 : Upper (D 7) (R 7) [6,288,96,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15423 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 290 100 88 145 40 195 131 387), lower := (rows 7 290 100 88 145 40 64 128 256), losses := [] }

theorem u15423 : Upper (D 7) (R 7) [6,288,96,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15423 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15424 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 7 290 100 88 145 160 75 139 267), lower := (rows 7 290 100 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 6 290 100 124 176 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 5 288 100 124 177 160 64 160 256) }] }

theorem u15424 : Upper (D 7) (R 7) [6,288,96,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15425 : Route 9 := (fun mask => (mask,id))

def c15425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15425 : Upper (D 7) (R 7) [6,288,96,80,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,96,80,130,1] 13 (by decide) (choices 1) [1,8,128] r15425 c15425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3194
  · exact u3195
  · exact u3196

def b15426 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 290 100 88 146 40 193 129 385), lower := (rows 7 290 100 88 146 40 64 128 256), losses := [] }

theorem u15426 : Upper (D 7) (R 7) [6,288,96,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15426 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15427 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 7 290 100 88 146 160 73 137 265), lower := (rows 7 290 100 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 6 290 100 124 178 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 5 288 100 124 176 160 64 160 256) }] }

theorem u15427 : Upper (D 7) (R 7) [6,288,96,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15428 : Route 9 := (fun mask => (mask,id))

def c15428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15428 : Upper (D 7) (R 7) [6,288,96,129,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,96,129,130,1] 13 (by decide) (choices 1) [8,16] r15428 c15428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3197
  · exact u3198

def r15429 : Route 9 := (fun mask => (mask,id))

def c15429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15429 : Upper (D 7) (R 7) [6,288,96,129,130,8] 13 := by
  apply FastRouting.sound _ _ [6,288,96,129,130,8] 13 (by decide) (choices 1) [1,16] r15429 c15429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3199
  · exact u3200

def b15430 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 290 100 137 146 48 73 201 329), lower := (rows 7 290 100 137 146 48 64 128 256), losses := [] }

theorem u15430 : Upper (D 7) (R 7) [6,288,96,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15430 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15431 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 290 100 137 146 96 89 153 281), lower := (rows 7 290 100 137 146 96 64 128 256), losses := [] }

theorem u15431 : Upper (D 7) (R 7) [6,288,96,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15432 : Route 9 := (fun mask => (mask,id))

def c15432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15432 : Upper (D 7) (R 7) [6,288,96,129,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,96,129,192,1] 13 (by decide) (choices 1) [2,8,16] r15432 c15432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3201
  · exact u3202
  · exact u3203

def b15433 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 100 137 208 34 89 153 281), lower := (rows 7 290 100 137 208 34 64 128 256), losses := [] }

theorem u15433 : Upper (D 7) (R 7) [6,288,96,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15434 : Route 9 := (fun mask => (mask,id))

def c15434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15434 : Upper (D 7) (R 7) [6,288,96,129,192,8] 13 := by
  apply FastRouting.sound _ _ [6,288,96,129,192,8] 13 (by decide) (choices 1) [1,2,16] r15434 c15434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3204
  · exact u3205
  · exact u3206

def b15435 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 100 137 208 48 75 139 267), lower := (rows 7 290 100 137 208 48 64 128 256), losses := [] }

theorem u15435 : Upper (D 7) (R 7) [6,288,96,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15435 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15436 : Route 9 := (fun mask => (mask,id))

def c15436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15436 : Upper (D 7) (R 7) [6,288,96,130,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,96,130,192,1] 13 (by decide) (choices 1) [1,8,16] r15436 c15436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3207
  · exact u3208
  · exact u3209

def b15437 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 290 100 138 208 40 81 145 273), lower := (rows 7 290 100 138 208 40 64 128 256), losses := [] }

theorem u15437 : Upper (D 7) (R 7) [6,288,96,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15437 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15438 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 100 138 208 48 73 137 265), lower := (rows 7 290 100 138 208 48 64 128 256), losses := [] }

theorem u15438 : Upper (D 7) (R 7) [6,288,96,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15438 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15439 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 56, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 7 290 196 25 56 33 194 194 450), lower := (rows 7 290 196 25 56 33 64 128 256), losses := [] }

theorem u15439 : Upper (D 7) (R 7) [6,288,192,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15440 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 290 196 25 56 34 193 193 449), lower := (rows 7 290 196 25 56 34 64 128 256), losses := [] }

theorem u15440 : Upper (D 7) (R 7) [6,288,192,17,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15441 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(3,1),(4,1)], upper := (rows 7 290 196 25 56 96 195 131 387), lower := (rows 7 290 196 25 56 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 100 64 128 256), good := (rows 61 288 228 25 56 96 96 128 256) }] }

theorem u15441 : Upper (D 7) (R 7) [6,288,192,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15442 : Route 9 := (fun mask => (mask,id))

def c15442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15442 : Upper (D 7) (R 7) [6,288,192,17,66,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17,66,1] 13 (by decide) (choices 1) [8,32,128] r15442 c15442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3210
  · exact u3211
  · exact u3212

def r15443 : Route 9 := (fun mask => (mask,id))

def c15443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15443 : Upper (D 7) (R 7) [6,288,192,17,66,8] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17,66,8] 13 (by decide) (choices 1) [1,32,128] r15443 c15443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3213
  · exact u3214
  · exact u3215

def r15444 : Route 9 := (fun mask => (mask,id))

def c15444 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15444 : Upper (D 7) (R 7) [6,288,192,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17,66,128] 13 (by decide) (choices 1) [1,8,32] r15444 c15444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3216
  · exact u3217
  · exact u3218

def b15445 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 5, region := 454, targets := 1 }], pairs := [(0,6),(1,0),(1,6),(2,0)], upper := (rows 7 290 196 25 88 33 226 162 418), lower := (rows 7 290 196 25 88 33 64 128 256), losses := [] }

theorem u15445 : Upper (D 7) (R 7) [6,288,192,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15446 : PairBound 9 := { available := 161, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 7 290 196 25 88 34 225 161 417), lower := (rows 7 290 196 25 88 34 64 128 256), losses := [] }

theorem u15446 : Upper (D 7) (R 7) [6,288,192,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15447 : Route 9 := (fun mask => (mask,id))

def c15447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15447 : Upper (D 7) (R 7) [6,288,192,17,72,128] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17,72,128] 13 (by decide) (choices 1) [1,2,32] r15447 c15447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3219
  · exact u3220
  · exact u3221

def r15448 : Route 9 := (fun mask => (mask,id))

def c15448 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15448 : Upper (D 7) (R 7) [6,288,192,17,96,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17,96,1] 13 (by decide) (choices 1) [2,8,128] r15448 c15448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3222
  · exact u3223
  · exact u3224

def b15449 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 290 196 25 112 34 201 137 393), lower := (rows 7 290 196 25 112 34 64 128 256), losses := [] }

theorem u15449 : Upper (D 7) (R 7) [6,288,192,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15450 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(2,5)], upper := (rows 7 290 196 25 112 40 195 131 387), lower := (rows 7 290 196 25 112 40 64 128 256), losses := [] }

theorem u15450 : Upper (D 7) (R 7) [6,288,192,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15450 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15451 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(3,1),(4,0),(4,1)], upper := (rows 7 290 196 25 112 160 75 139 267), lower := (rows 7 290 196 25 112 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 20 164 64 128 256), good := (rows 61 288 244 25 112 160 64 160 256) }] }

theorem u15451 : Upper (D 7) (R 7) [6,288,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15452 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 290 196 26 49 33 200 200 456), lower := (rows 7 290 196 26 49 33 64 128 256), losses := [] }

theorem u15452 : Upper (D 7) (R 7) [6,288,192,18,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15453 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6)], upper := (rows 7 290 196 26 49 40 193 193 449), lower := (rows 7 290 196 26 49 40 64 128 256), losses := [] }

theorem u15453 : Upper (D 7) (R 7) [6,288,192,18,33,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15453 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15454 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 197, targets := 32 },{ cop := 4, region := 394, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,6)], upper := (rows 7 290 196 26 49 96 201 137 393), lower := (rows 7 290 196 26 49 96 64 128 256), losses := [] }

theorem u15454 : Upper (D 7) (R 7) [6,288,192,18,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15455 : Route 9 := (fun mask => (mask,id))

def c15455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15455 : Upper (D 7) (R 7) [6,288,192,18,65,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,65,1] 13 (by decide) (choices 1) [8,32,128] r15455 c15455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3225
  · exact u3226
  · exact u3227

def r15456 : Route 9 := (fun mask => (mask,id))

def c15456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15456 : Upper (D 7) (R 7) [6,288,192,18,65,8] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,65,8] 13 (by decide) (choices 1) [1,32,128] r15456 c15456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3228
  · exact u3229
  · exact u3230

def r15457 : Route 9 := (fun mask => (mask,id))

def c15457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15457 : Upper (D 7) (R 7) [6,288,192,18,65,128] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,65,128] 13 (by decide) (choices 1) [1,8,32] r15457 c15457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3231
  · exact u3232
  · exact u3233

def r15458 : Route 9 := (fun mask => (mask,id))

def c15458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15458 : Upper (D 7) (R 7) [6,288,192,18,72,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,72,1] 13 (by decide) (choices 1) [1,32,128] r15458 c15458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3234
  · exact u3235
  · exact u3236

def r15459 : Route 9 := (fun mask => (mask,id))

def c15459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15459 : Upper (D 7) (R 7) [6,288,192,18,72,128] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,72,128] 13 (by decide) (choices 1) [1,32] r15459 c15459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3237
  · exact u3238

def r15460 : Route 9 := (fun mask => (mask,id))

def c15460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15460 : Upper (D 7) (R 7) [6,288,192,18,96,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,96,1] 13 (by decide) (choices 1) [1,8,128] r15460 c15460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3239
  · exact u3240
  · exact u3241

def b15461 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,1),(2,5)], upper := (rows 7 290 196 26 112 40 193 129 385), lower := (rows 7 290 196 26 112 40 64 128 256), losses := [] }

theorem u15461 : Upper (D 7) (R 7) [6,288,192,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15461 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15462 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,1)], upper := (rows 7 290 196 26 112 160 73 137 265), lower := (rows 7 290 196 26 112 160 64 128 256), losses := [] }

theorem u15462 : Upper (D 7) (R 7) [6,288,192,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15463 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 196 41 81 34 216 152 408), lower := (rows 7 290 196 41 81 34 64 128 256), losses := [] }

theorem u15463 : Upper (D 7) (R 7) [6,288,192,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15464 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 290 196 41 81 40 210 146 402), lower := (rows 7 290 196 41 81 40 64 128 256), losses := [] }

theorem u15464 : Upper (D 7) (R 7) [6,288,192,33,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15464 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15465 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 1 },{ cop := 4, region := 40, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 7 290 196 41 81 48 202 138 394), lower := (rows 7 290 196 41 81 48 64 128 256), losses := [] }

theorem u15465 : Upper (D 7) (R 7) [6,288,192,33,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15465 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15466 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(1,7),(3,6),(4,7)], upper := (rows 7 290 196 41 81 160 90 154 282), lower := (rows 7 290 196 41 81 160 64 128 256), losses := [] }

theorem u15466 : Upper (D 7) (R 7) [6,288,192,33,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15467 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 290 196 41 82 33 216 152 408), lower := (rows 7 290 196 41 82 33 64 128 256), losses := [] }

theorem u15467 : Upper (D 7) (R 7) [6,288,192,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15468 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 290 196 41 82 40 209 145 401), lower := (rows 7 290 196 41 82 40 64 128 256), losses := [] }

theorem u15468 : Upper (D 7) (R 7) [6,288,192,33,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15468 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15469 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 196, targets := 34 },{ cop := 3, region := 386, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 7 290 196 41 82 48 201 137 393), lower := (rows 7 290 196 41 82 48 64 128 256), losses := [] }

theorem u15469 : Upper (D 7) (R 7) [6,288,192,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15469 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15470 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7),(3,1),(3,6),(4,7)], upper := (rows 7 290 196 41 82 160 89 153 281), lower := (rows 7 290 196 41 82 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 164 64 128 256), good := (rows 45 288 228 41 80 160 64 160 256) },{ target := 6, region := (rows 1 2 4 9 16 164 0 128 256), good := (rows 47 290 164 41 18 160 0 160 256) }] }

theorem u15470 : Upper (D 7) (R 7) [6,288,192,33,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15471 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 290 196 41 88 33 210 146 402), lower := (rows 7 290 196 41 88 33 64 128 256), losses := [] }

theorem u15471 : Upper (D 7) (R 7) [6,288,192,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15472 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 196 41 88 34 209 145 401), lower := (rows 7 290 196 41 88 34 64 128 256), losses := [] }

theorem u15472 : Upper (D 7) (R 7) [6,288,192,33,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15473 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 386, targets := 64 }], pairs := [(0,5),(1,6),(2,5)], upper := (rows 7 290 196 41 88 48 195 131 387), lower := (rows 7 290 196 41 88 48 64 128 256), losses := [] }

theorem u15473 : Upper (D 7) (R 7) [6,288,192,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15473 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15474 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7),(3,1),(3,6),(4,7)], upper := (rows 7 290 196 41 88 160 83 147 275), lower := (rows 7 290 196 41 88 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 164 64 128 256), good := (rows 45 288 228 41 88 160 64 160 256) },{ target := 6, region := (rows 1 2 4 9 16 164 0 128 256), good := (rows 47 290 164 41 24 160 0 160 256) }] }

theorem u15474 : Upper (D 7) (R 7) [6,288,192,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15475 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 1 },{ cop := 4, region := 40, targets := 130 }], pairs := [(1,0),(2,0),(3,1),(3,7)], upper := (rows 7 290 196 56 81 33 202 138 394), lower := (rows 7 290 196 56 81 33 64 128 256), losses := [] }

theorem u15475 : Upper (D 7) (R 7) [6,288,192,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15476 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 7 290 196 56 81 34 201 137 393), lower := (rows 7 290 196 56 81 34 64 128 256), losses := [] }

theorem u15476 : Upper (D 7) (R 7) [6,288,192,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15477 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 196 56 81 40 195 131 387), lower := (rows 7 290 196 56 81 40 64 128 256), losses := [] }

theorem u15477 : Upper (D 7) (R 7) [6,288,192,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15477 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15478 : Route 9 := (fun mask => (mask,id))

def c15478 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15478 : Upper (D 7) (R 7) [6,288,192,48,65,128] 13 := by
  apply FastRouting.sound _ _ [6,288,192,48,65,128] 13 (by decide) (choices 1) [1,2,8] r15478 c15478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3242
  · exact u3243
  · exact u3244

def r15479 : Route 9 := (fun mask => (mask,id))

def c15479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15479 : Upper (D 7) (R 7) [6,288,192,48,66,1] 13 := by
  apply FastRouting.sound _ _ [6,288,192,48,66,1] 13 (by decide) (choices 1) [1,8,128] r15479 c15479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3245
  · exact u3246
  · exact u3247

#print axioms u15479
end Delivery.IrregularNine14.P07
