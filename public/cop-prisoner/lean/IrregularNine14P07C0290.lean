import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0071

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17400 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 38 104 145 96 210 146 402), lower := (rows 13 259 38 104 145 96 64 128 256), losses := [] }

theorem u17400 : Upper (D 7) (R 7) [12,257,34,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17401 : Route 9 := (fun mask => (mask,id))

def c17401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17401 : Upper (D 7) (R 7) [12,257,34,96,129,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,96,129,128] 13 (by decide) (choices 1) [2,16] r17401 c17401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4264
  · exact u4265

def b17402 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 36, targets := 192 }], pairs := [(1,5),(2,6),(2,7),(4,5)], upper := (rows 13 259 38 104 146 33 208 208 464), lower := (rows 13 259 38 104 146 33 64 128 256), losses := [] }

theorem u17402 : Upper (D 7) (R 7) [12,257,34,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17403 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 13 259 38 104 146 48 193 193 449), lower := (rows 13 259 38 104 146 48 64 128 256), losses := [] }

theorem u17403 : Upper (D 7) (R 7) [12,257,34,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17403 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17404 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 38 104 146 96 209 145 401), lower := (rows 13 259 38 104 146 96 64 128 256), losses := [] }

theorem u17404 : Upper (D 7) (R 7) [12,257,34,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17405 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 36, targets := 65 }], pairs := [(1,5),(2,0),(2,6),(4,5)], upper := (rows 13 259 38 104 146 160 81 209 337), lower := (rows 13 259 38 104 146 160 64 128 256), losses := [] }

theorem u17405 : Upper (D 7) (R 7) [12,257,34,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17406 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 36, targets := 192 }], pairs := [(1,5),(2,6),(2,7),(4,5)], upper := (rows 13 259 38 104 208 33 210 146 402), lower := (rows 13 259 38 104 208 33 64 128 256), losses := [] }

theorem u17406 : Upper (D 7) (R 7) [12,257,34,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17407 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 259 38 104 208 34 209 145 401), lower := (rows 13 259 38 104 208 34 64 128 256), losses := [] }

theorem u17407 : Upper (D 7) (R 7) [12,257,34,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17408 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 13 259 38 104 208 48 195 131 387), lower := (rows 13 259 38 104 208 48 64 128 256), losses := [] }

theorem u17408 : Upper (D 7) (R 7) [12,257,34,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17409 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 3 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 13 259 38 104 208 160 83 147 275), lower := (rows 13 259 38 104 208 160 64 128 256), losses := [] }

theorem u17409 : Upper (D 7) (R 7) [12,257,34,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17410 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 52, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 259 38 200 49 34 208 208 464), lower := (rows 13 259 38 200 49 34 64 128 256), losses := [] }

theorem u17410 : Upper (D 7) (R 7) [12,257,34,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17411 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 52, targets := 192 }], pairs := [(2,6),(2,7),(4,6)], upper := (rows 13 259 38 200 49 48 194 194 450), lower := (rows 13 259 38 200 49 48 64 128 256), losses := [] }

theorem u17411 : Upper (D 7) (R 7) [12,257,34,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17411 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17412 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 390, targets := 64 }], pairs := [(1,5),(1,6),(2,6),(3,5)], upper := (rows 13 259 38 200 49 96 210 146 402), lower := (rows 13 259 38 200 49 96 64 128 256), losses := [] }

theorem u17412 : Upper (D 7) (R 7) [12,257,34,192,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17413 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 259 38 200 81 34 240 176 432), lower := (rows 13 259 38 200 81 34 64 128 256), losses := [] }

theorem u17413 : Upper (D 7) (R 7) [12,257,34,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17414 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 2, region := 200, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 13 259 38 200 81 48 226 162 418), lower := (rows 13 259 38 200 81 48 64 128 256), losses := [] }

theorem u17414 : Upper (D 7) (R 7) [12,257,34,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17414 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17415 : Route 9 := (fun mask => (mask,id))

def c17415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17415 : Upper (D 7) (R 7) [12,257,34,192,65,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,192,65,128] 13 (by decide) (choices 1) [2,16,32] r17415 c17415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4266
  · exact u4267
  · exact u4268

def b17416 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 36, targets := 192 },{ cop := 2, region := 216, targets := 1 }], pairs := [(2,6),(2,7),(3,0),(4,0)], upper := (rows 13 259 38 200 82 33 240 176 432), lower := (rows 13 259 38 200 82 33 64 128 256), losses := [] }

theorem u17416 : Upper (D 7) (R 7) [12,257,34,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17417 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 13 259 38 200 82 48 225 161 417), lower := (rows 13 259 38 200 82 48 64 128 256), losses := [] }

theorem u17417 : Upper (D 7) (R 7) [12,257,34,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17417 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17418 : Route 9 := (fun mask => (mask,id))

def c17418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17418 : Upper (D 7) (R 7) [12,257,34,192,66,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,192,66,128] 13 (by decide) (choices 1) [1,16,32] r17418 c17418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4269
  · exact u4270
  · exact u4271

def b17419 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 36, targets := 192 },{ cop := 2, region := 216, targets := 1 }], pairs := [(2,6),(2,7),(3,0),(4,0)], upper := (rows 13 259 38 200 112 33 210 146 402), lower := (rows 13 259 38 200 112 33 64 128 256), losses := [] }

theorem u17419 : Upper (D 7) (R 7) [12,257,34,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17420 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 259 38 200 112 34 209 145 401), lower := (rows 13 259 38 200 112 34 64 128 256), losses := [] }

theorem u17420 : Upper (D 7) (R 7) [12,257,34,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17421 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 13 259 38 200 112 48 195 131 387), lower := (rows 13 259 38 200 112 48 64 128 256), losses := [] }

theorem u17421 : Upper (D 7) (R 7) [12,257,34,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17421 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17422 : Route 9 := (fun mask => (mask,id))

def c17422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17422 : Upper (D 7) (R 7) [12,257,34,192,96,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,192,96,128] 13 (by decide) (choices 1) [1,2,16] r17422 c17422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4272
  · exact u4273
  · exact u4274

def r17423 : Route 9 := (fun mask => (mask,id))

def c17423 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17423 : Upper (D 7) (R 7) [12,257,48,96,129,2] 13 := by
  apply FastRouting.sound _ _ [12,257,48,96,129,2] 13 (by decide) (choices 1) [2,128] r17423 c17423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4275
  · exact u4276

def b17424 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 52 104 145 96 194 130 386), lower := (rows 13 259 52 104 145 96 64 128 256), losses := [] }

theorem u17424 : Upper (D 7) (R 7) [12,257,48,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17425 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 259 52 104 145 160 66 194 322), lower := (rows 13 259 52 104 145 160 64 128 256), losses := [] }

theorem u17425 : Upper (D 7) (R 7) [12,257,48,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17426 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 208, targets := 1 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 13 259 52 104 146 33 194 194 450), lower := (rows 13 259 52 104 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 18 32 82 146 274), good := (rows 12 466 508 104 466 32 64 128 256) }] }

theorem u17426 : Upper (D 7) (R 7) [12,257,48,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17427 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 36, targets := 193 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,0),(2,6),(2,7)], upper := (rows 13 259 52 104 146 34 193 193 449), lower := (rows 13 259 52 104 146 34 64 128 256), losses := [] }

theorem u17427 : Upper (D 7) (R 7) [12,257,48,96,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17428 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 52 104 146 96 195 131 387), lower := (rows 13 259 52 104 146 96 64 128 256), losses := [] }

theorem u17428 : Upper (D 7) (R 7) [12,257,48,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17429 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 259 52 104 146 160 67 195 323), lower := (rows 13 259 52 104 146 160 64 128 256), losses := [] }

theorem u17429 : Upper (D 7) (R 7) [12,257,48,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17430 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 259 52 104 208 33 194 130 386), lower := (rows 13 259 52 104 208 33 64 128 256), losses := [] }

theorem u17430 : Upper (D 7) (R 7) [12,257,48,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17431 : Route 9 := (fun mask => (mask,id))

def c17431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17431 : Upper (D 7) (R 7) [12,257,48,96,192,2] 13 := by
  apply FastRouting.sound _ _ [12,257,48,96,192,2] 13 (by decide) (choices 1) [1,2,128] r17431 c17431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4277
  · exact u4278
  · exact u4279

def b17432 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,7)], upper := (rows 13 259 52 104 208 160 67 131 259), lower := (rows 13 259 52 104 208 160 64 128 256), losses := [] }

theorem u17432 : Upper (D 7) (R 7) [12,257,48,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17433 : Route 9 := (fun mask => (mask,id))

def c17433 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17433 : Upper (D 7) (R 7) [12,257,48,192,65,2] 13 := by
  apply FastRouting.sound _ _ [12,257,48,192,65,2] 13 (by decide) (choices 1) [2,32,128] r17433 c17433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4280
  · exact u4281
  · exact u4282

def b17434 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 4, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(4,1)], upper := (rows 13 259 52 200 81 160 98 162 290), lower := (rows 13 259 52 200 81 160 64 128 256), losses := [] }

theorem u17434 : Upper (D 7) (R 7) [12,257,48,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17435 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(2,1),(2,6),(2,7)], upper := (rows 13 259 52 200 82 33 226 162 418), lower := (rows 13 259 52 200 82 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 35 64 128 256), good := (rows 45 289 52 200 116 33 64 128 256) },{ target := 6, region := (rows 1 35 20 8 16 35 0 183 311), good := (rows 431 419 438 136 438 419 0 128 256) },{ target := 7, region := (rows 1 2 20 8 16 35 64 0 256), good := (rows 45 291 52 72 118 33 64 0 256) }] }

theorem u17435 : Upper (D 7) (R 7) [12,257,48,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17436 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 36, targets := 193 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 259 52 200 82 34 225 161 417), lower := (rows 13 259 52 200 82 34 64 128 256), losses := [] }

theorem u17436 : Upper (D 7) (R 7) [12,257,48,192,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17437 : Route 9 := (fun mask => (mask,id))

def c17437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17437 : Upper (D 7) (R 7) [12,257,48,192,66,128] 13 := by
  apply FastRouting.sound _ _ [12,257,48,192,66,128] 13 (by decide) (choices 1) [1,2,32] r17437 c17437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4283
  · exact u4284
  · exact u4285

def b17438 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 208, targets := 1 }], pairs := [(1,5),(2,1),(4,0),(4,5)], upper := (rows 13 259 100 168 82 33 210 146 402), lower := (rows 13 259 100 168 82 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 35 64 128 256), good := (rows 45 289 100 168 116 33 64 128 256) }] }

theorem u17438 : Upper (D 7) (R 7) [12,257,96,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17439 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 36, targets := 129 }], pairs := [(1,5),(2,0),(2,7),(4,5)], upper := (rows 13 259 100 168 82 34 209 145 401), lower := (rows 13 259 100 168 82 34 64 128 256), losses := [] }

theorem u17439 : Upper (D 7) (R 7) [12,257,96,160,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17440 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 259 100 168 82 48 195 131 387), lower := (rows 13 259 100 168 82 48 64 128 256), losses := [] }

theorem u17440 : Upper (D 7) (R 7) [12,257,96,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17440 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17441 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 259 100 168 82 160 83 147 275), lower := (rows 13 259 100 168 82 160 64 128 256), losses := [] }

theorem u17441 : Upper (D 7) (R 7) [12,257,96,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17442 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 13 259 100 168 208 33 82 146 274), lower := (rows 13 259 100 168 208 33 64 128 256), losses := [] }

theorem u17442 : Upper (D 7) (R 7) [12,257,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17443 : Route 9 := (fun mask => (mask,id))

def c17443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17443 : Upper (D 7) (R 7) [12,257,96,160,192,2] 13 := by
  apply FastRouting.sound _ _ [12,257,96,160,192,2] 13 (by decide) (choices 1) [1,2,16] r17443 c17443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4286
  · exact u4287
  · exact u4288

def b17444 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 259 100 168 208 48 67 131 259), lower := (rows 13 259 100 168 208 48 64 128 256), losses := [] }

theorem u17444 : Upper (D 7) (R 7) [12,257,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17444 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17445 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 7 41 112 34 192 192 448), lower := (rows 13 274 7 41 112 34 64 128 256), losses := [] }

theorem u17445 : Upper (D 7) (R 7) [12,272,3,33,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17446 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 13 274 7 41 112 96 194 130 386), lower := (rows 13 274 7 41 112 96 64 128 256), losses := [] }

theorem u17446 : Upper (D 7) (R 7) [12,272,3,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17447 : Route 9 := (fun mask => (mask,id))

def c17447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17447 : Upper (D 7) (R 7) [12,272,3,33,96,128] 13 := by
  apply FastRouting.sound _ _ [12,272,3,33,96,128] 13 (by decide) (choices 1) [2,128] r17447 c17447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4289
  · exact u4290

def b17448 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 7 41 208 34 224 224 480), lower := (rows 13 274 7 41 208 34 64 128 256), losses := [] }

theorem u17448 : Upper (D 7) (R 7) [12,272,3,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17449 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 13 274 7 41 208 96 226 162 418), lower := (rows 13 274 7 41 208 96 64 128 256), losses := [{ target := 7, region := (rows 7 2 6 10 16 112 64 0 256), good := (rows 13 319 15 41 112 96 96 0 256) }] }

theorem u17449 : Upper (D 7) (R 7) [12,272,3,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17450 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 274 7 104 50 33 192 192 448), lower := (rows 13 274 7 104 50 33 64 128 256), losses := [] }

theorem u17450 : Upper (D 7) (R 7) [12,272,3,96,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17451 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 274 7 104 50 96 193 129 385), lower := (rows 13 274 7 104 50 96 64 128 256), losses := [] }

theorem u17451 : Upper (D 7) (R 7) [12,272,3,96,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17452 : Route 9 := (fun mask => (mask,id))

def c17452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17452 : Upper (D 7) (R 7) [12,272,3,96,34,128] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96,34,128] 13 (by decide) (choices 1) [1,128] r17452 c17452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4291
  · exact u4292

def b17453 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 5, region := 200, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,1)], upper := (rows 13 274 7 104 145 34 224 224 480), lower := (rows 13 274 7 104 145 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 40 17 32 104 168 296), good := (rows 477 272 21 488 145 488 64 128 256) }] }

theorem u17453 : Upper (D 7) (R 7) [12,272,3,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17454 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 274 7 104 145 96 226 162 418), lower := (rows 13 274 7 104 145 96 64 128 256), losses := [] }

theorem u17454 : Upper (D 7) (R 7) [12,272,3,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17455_2 : Upper (D 7) (R 7) [12,272,3,96,129,128,2] 13 :=
  permutation_upper _ _ _ [12,272,3,96,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4293

theorem m17455_32 : Upper (D 7) (R 7) [12,272,3,96,129,128,32] 13 :=
  permutation_upper _ _ _ [12,272,3,96,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4294

def r17455 : Route 9 := (fun mask => (mask,id))

def c17455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17455 : Upper (D 7) (R 7) [12,272,3,96,129,128] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96,129,128] 13 (by decide) (choices 1) [2,32] r17455 c17455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17455_2
  · exact m17455_32

def b17456 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 274 7 104 146 33 224 224 480), lower := (rows 13 274 7 104 146 33 64 128 256), losses := [] }

theorem u17456 : Upper (D 7) (R 7) [12,272,3,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17457 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 274 7 104 146 96 225 161 417), lower := (rows 13 274 7 104 146 96 64 128 256), losses := [] }

theorem u17457 : Upper (D 7) (R 7) [12,272,3,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17458_1 : Upper (D 7) (R 7) [12,272,3,96,130,128,1] 13 :=
  permutation_upper _ _ _ [12,272,3,96,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4295

theorem m17458_32 : Upper (D 7) (R 7) [12,272,3,96,130,128,32] 13 :=
  permutation_upper _ _ _ [12,272,3,96,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4296

def r17458 : Route 9 := (fun mask => (mask,id))

def c17458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17458 : Upper (D 7) (R 7) [12,272,3,96,130,128] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96,130,128] 13 (by decide) (choices 1) [1,32] r17458 c17458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17458_1
  · exact m17458_32

def b17459 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 322, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,0)], upper := (rows 13 274 7 104 176 33 194 194 450), lower := (rows 13 274 7 104 176 33 64 128 256), losses := [] }

theorem u17459 : Upper (D 7) (R 7) [12,272,3,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17459
end Delivery.IrregularNine14.P07
