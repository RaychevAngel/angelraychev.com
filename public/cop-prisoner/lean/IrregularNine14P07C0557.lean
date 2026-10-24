import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0289
import IrregularNine14P07C0290
import IrregularNine14P07C0291

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33420 : Route 9 := (fun mask => (mask,id))

def c33420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33420 : Upper (D 7) (R 7) [12,257,34,96,66] 13 := by
  apply FastRouting.sound _ _ [12,257,34,96,66] 13 (by decide) (choices 1) [1,16,128] r33420 c33420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17395
  · exact u17396
  · exact u17397

def r33421 : Route 9 := (fun mask => (mask,id))

def c33421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33421 : Upper (D 7) (R 7) [12,257,34,96,129] 13 := by
  apply FastRouting.sound _ _ [12,257,34,96,129] 13 (by decide) (choices 1) [2,16,64,128] r33421 c33421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17398
  · exact u17399
  · exact u17400
  · exact u17401

def r33422 : Route 9 := (fun mask => (mask,id))

def c33422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33422 : Upper (D 7) (R 7) [12,257,34,96,130] 13 := by
  apply FastRouting.sound _ _ [12,257,34,96,130] 13 (by decide) (choices 1) [1,16,64,128] r33422 c33422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17402
  · exact u17403
  · exact u17404
  · exact u17405

def r33423 : Route 9 := (fun mask => (mask,id))

def c33423 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33423 : Upper (D 7) (R 7) [12,257,34,96,192] 13 := by
  apply FastRouting.sound _ _ [12,257,34,96,192] 13 (by decide) (choices 1) [1,2,16,128] r33423 c33423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17406
  · exact u17407
  · exact u17408
  · exact u17409

def b33424 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 259 38 200 19 240 240 240 496), lower := (rows 13 259 38 200 19 32 64 128 256), losses := [] }

theorem u33424 : Upper (D 7) (R 7) [12,257,34,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33425 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33425 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33425 : Upper (D 7) (R 7) [12,257,34,192,33] 13 := by
  apply FastRouting.sound _ _ [12,257,34,192,33] 13 (by decide) (choices 1) [2,16,64] r33425 c33425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17410
  · exact u17411
  · exact u17412

def b33426 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 16, targets := 193 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,6),(4,7)], upper := (rows 13 259 38 200 50 241 209 209 465), lower := (rows 13 259 38 200 50 32 64 128 256), losses := [] }

theorem u33426 : Upper (D 7) (R 7) [12,257,34,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33427 : Route 9 := (fun mask => (mask,id))

def c33427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33427 : Upper (D 7) (R 7) [12,257,34,192,65] 13 := by
  apply FastRouting.sound _ _ [12,257,34,192,65] 13 (by decide) (choices 1) [2,16,128] r33427 c33427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17413
  · exact u17414
  · exact u17415

def r33428 : Route 9 := (fun mask => (mask,id))

def c33428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33428 : Upper (D 7) (R 7) [12,257,34,192,66] 13 := by
  apply FastRouting.sound _ _ [12,257,34,192,66] 13 (by decide) (choices 1) [1,16,128] r33428 c33428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17416
  · exact u17417
  · exact u17418

def r33429 : Route 9 := (fun mask => (mask,id))

def c33429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33429 : Upper (D 7) (R 7) [12,257,34,192,96] 13 := by
  apply FastRouting.sound _ _ [12,257,34,192,96] 13 (by decide) (choices 1) [1,2,16,128] r33429 c33429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17419
  · exact u17420
  · exact u17421
  · exact u17422

def b33430 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 259 38 200 208 51 115 179 307), lower := (rows 13 259 38 200 208 32 64 128 256), losses := [] }

theorem u33430 : Upper (D 7) (R 7) [12,257,34,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33431 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 13 259 52 104 19 226 194 194 450), lower := (rows 13 259 52 104 19 32 64 128 256), losses := [] }

theorem u33431 : Upper (D 7) (R 7) [12,257,48,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33432 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 21, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 259 52 104 81 162 194 130 386), lower := (rows 13 259 52 104 81 32 64 128 256), losses := [] }

theorem u33432 : Upper (D 7) (R 7) [12,257,48,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33433 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,6),(4,5)], upper := (rows 13 259 52 104 82 163 195 131 387), lower := (rows 13 259 52 104 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 20 8 16 35 0 131 259), good := (rows 431 419 52 40 438 32 0 128 256) }] }

theorem u33433 : Upper (D 7) (R 7) [12,257,48,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33434 : Route 9 := (fun mask => (mask,id))

def c33434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33434 : Upper (D 7) (R 7) [12,257,48,96,129] 13 := by
  apply FastRouting.sound _ _ [12,257,48,96,129] 13 (by decide) (choices 1) [2,64,128] r33434 c33434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17423
  · exact u17424
  · exact u17425

def r33435 : Route 9 := (fun mask => (mask,id))

def c33435 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33435 : Upper (D 7) (R 7) [12,257,48,96,130] 13 := by
  apply FastRouting.sound _ _ [12,257,48,96,130] 13 (by decide) (choices 1) [1,2,64,128] r33435 c33435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17426
  · exact u17427
  · exact u17428
  · exact u17429

def r33436 : Route 9 := (fun mask => (mask,id))

def c33436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33436 : Upper (D 7) (R 7) [12,257,48,96,192] 13 := by
  apply FastRouting.sound _ _ [12,257,48,96,192] 13 (by decide) (choices 1) [1,2,128] r33436 c33436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17430
  · exact u17431
  · exact u17432

def b33437 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 13 259 52 200 19 226 226 226 482), lower := (rows 13 259 52 200 19 32 64 128 256), losses := [] }

theorem u33437 : Upper (D 7) (R 7) [12,257,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33438 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 13 259 52 200 49 226 194 194 450), lower := (rows 13 259 52 200 49 32 64 128 256), losses := [] }

theorem u33438 : Upper (D 7) (R 7) [12,257,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33439 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 13 259 52 200 50 227 195 195 451), lower := (rows 13 259 52 200 50 32 64 128 256), losses := [] }

theorem u33439 : Upper (D 7) (R 7) [12,257,48,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33440 : Route 9 := (fun mask => (mask,id))

def c33440 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33440 : Upper (D 7) (R 7) [12,257,48,192,65] 13 := by
  apply FastRouting.sound _ _ [12,257,48,192,65] 13 (by decide) (choices 1) [2,128] r33440 c33440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17433
  · exact u17434

def r33441 : Route 9 := (fun mask => (mask,id))

def c33441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33441 : Upper (D 7) (R 7) [12,257,48,192,66] 13 := by
  apply FastRouting.sound _ _ [12,257,48,192,66] 13 (by decide) (choices 1) [1,2,128] r33441 c33441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17435
  · exact u17436
  · exact u17437

def b33442 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 13 259 52 200 112 163 195 131 387), lower := (rows 13 259 52 200 112 32 64 128 256), losses := [] }

theorem u33442 : Upper (D 7) (R 7) [12,257,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33443 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 259 52 200 208 35 99 163 291), lower := (rows 13 259 52 200 208 32 64 128 256), losses := [] }

theorem u33443 : Upper (D 7) (R 7) [12,257,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33444 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 13 259 100 168 19 242 210 210 466), lower := (rows 13 259 100 168 19 32 64 128 256), losses := [] }

theorem u33444 : Upper (D 7) (R 7) [12,257,96,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33445 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,5),(1,6),(3,6),(4,5)], upper := (rows 13 259 100 168 81 178 210 146 402), lower := (rows 13 259 100 168 81 32 64 128 256), losses := [] }

theorem u33445 : Upper (D 7) (R 7) [12,257,96,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33446 : Route 9 := (fun mask => (mask,id))

def c33446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33446 : Upper (D 7) (R 7) [12,257,96,160,66] 13 := by
  apply FastRouting.sound _ _ [12,257,96,160,66] 13 (by decide) (choices 1) [1,2,16,128] r33446 c33446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17438
  · exact u17439
  · exact u17440
  · exact u17441

def r33447 : Route 9 := (fun mask => (mask,id))

def c33447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33447 : Upper (D 7) (R 7) [12,257,96,160,192] 13 := by
  apply FastRouting.sound _ _ [12,257,96,160,192] 13 (by decide) (choices 1) [1,2,16] r33447 c33447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17442
  · exact u17443
  · exact u17444

def b33448 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 7 41 50 224 192 192 448), lower := (rows 13 274 7 41 50 32 64 128 256), losses := [] }

theorem u33448 : Upper (D 7) (R 7) [12,272,3,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33449 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,1),(4,0)], upper := (rows 13 274 7 41 82 224 224 224 480), lower := (rows 13 274 7 41 82 32 64 128 256), losses := [] }

theorem u33449 : Upper (D 7) (R 7) [12,272,3,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33450 : Route 9 := (fun mask => (mask,id))

def c33450 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33450 : Upper (D 7) (R 7) [12,272,3,33,96] 13 := by
  apply FastRouting.sound _ _ [12,272,3,33,96] 13 (by decide) (choices 1) [2,64,128] r33450 c33450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17445
  · exact u17446
  · exact u17447

def r33451 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33451 : Upper (D 7) (R 7) [12,272,3,33,192] 13 := by
  apply FastRouting.sound _ _ [12,272,3,33,192] 13 (by decide) (choices 1) [2,64] r33451 c33451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17448
  · exact u17449

def b33452 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 274 7 104 19 224 224 224 480), lower := (rows 13 274 7 104 19 32 64 128 256), losses := [] }

theorem u33452 : Upper (D 7) (R 7) [12,272,3,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33453 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(3,0)], upper := (rows 13 274 7 104 49 226 194 194 450), lower := (rows 13 274 7 104 49 32 64 128 256), losses := [] }

theorem u33453 : Upper (D 7) (R 7) [12,272,3,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33454 : Route 9 := (fun mask => (mask,id))

def c33454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33454 : Upper (D 7) (R 7) [12,272,3,96,34] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96,34] 13 (by decide) (choices 1) [1,64,128] r33454 c33454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17450
  · exact u17451
  · exact u17452

def b33455 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 16, targets := 131 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,7)], upper := (rows 13 274 7 104 112 163 195 131 387), lower := (rows 13 274 7 104 112 32 64 128 256), losses := [] }

theorem u33455 : Upper (D 7) (R 7) [12,272,3,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33456 : Route 9 := (fun mask => (mask,id))

def c33456 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33456 : Upper (D 7) (R 7) [12,272,3,96,129] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96,129] 13 (by decide) (choices 1) [2,64,128] r33456 c33456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17453
  · exact u17454
  · exact u17455

def r33457 : Route 9 := (fun mask => (mask,id))

def c33457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33457 : Upper (D 7) (R 7) [12,272,3,96,130] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96,130] 13 (by decide) (choices 1) [1,64,128] r33457 c33457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17456
  · exact u17457
  · exact u17458

def r33458 : Route 9 := (fun mask => (mask,id))

def c33458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33458 : Upper (D 7) (R 7) [12,272,3,96,160] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96,160] 13 (by decide) (choices 1) [1,2,64,128] r33458 c33458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17459
  · exact u17460
  · exact u17461
  · exact u17462

def r33459 : Route 9 := (fun mask => (mask,id))

def c33459 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33459 : Upper (D 7) (R 7) [12,272,33,65,34] 13 := by
  apply FastRouting.sound _ _ [12,272,33,65,34] 13 (by decide) (choices 1) [2,64,128] r33459 c33459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17463
  · exact u17464
  · exact u17465

def b33460 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 73 112 162 194 130 386), lower := (rows 13 274 37 73 112 32 64 128 256), losses := [] }

theorem u33460 : Upper (D 7) (R 7) [12,272,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33461 : Route 9 := (fun mask => (mask,id))

def c33461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33461 : Upper (D 7) (R 7) [12,272,33,65,130] 13 := by
  apply FastRouting.sound _ _ [12,272,33,65,130] 13 (by decide) (choices 1) [2,64,128] r33461 c33461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17466
  · exact u17467
  · exact u17468

def r33462 : Route 9 := (fun mask => (mask,id))

def c33462 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33462 : Upper (D 7) (R 7) [12,272,33,65,160] 13 := by
  apply FastRouting.sound _ _ [12,272,33,65,160] 13 (by decide) (choices 1) [2,64,128] r33462 c33462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17469
  · exact u17470
  · exact u17471

def b33463 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 4, region := 490, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 13 274 37 74 19 224 224 224 480), lower := (rows 13 274 37 74 19 32 64 128 256), losses := [] }

theorem u33463 : Upper (D 7) (R 7) [12,272,33,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33464 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 16, targets := 194 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6),(4,7)], upper := (rows 13 274 37 74 49 226 194 194 450), lower := (rows 13 274 37 74 49 32 64 128 256), losses := [] }

theorem u33464 : Upper (D 7) (R 7) [12,272,33,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33465 : Route 9 := (fun mask => (mask,id))

def c33465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33465 : Upper (D 7) (R 7) [12,272,33,66,34] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,34] 13 (by decide) (choices 1) [1,64,128] r33465 c33465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17472
  · exact u17473
  · exact u17474

def b33466 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 13 274 37 74 81 162 226 162 418), lower := (rows 13 274 37 74 81 32 64 128 256), losses := [] }

theorem u33466 : Upper (D 7) (R 7) [12,272,33,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33467 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 13 274 37 74 82 161 225 161 417), lower := (rows 13 274 37 74 82 32 64 128 256), losses := [] }

theorem u33467 : Upper (D 7) (R 7) [12,272,33,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33468 : Route 9 := (fun mask => (mask,id))

def c33468 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33468 : Upper (D 7) (R 7) [12,272,33,66,96] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,96] 13 (by decide) (choices 1) [1,2,128] r33468 c33468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17475
  · exact u17476
  · exact u17477

def r33469 : Route 9 := (fun mask => (mask,id))

def c33469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33469 : Upper (D 7) (R 7) [12,272,33,66,129] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,129] 13 (by decide) (choices 1) [2,64,128] r33469 c33469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17478
  · exact u17479
  · exact u17480

def r33470 : Route 9 := (fun mask => (mask,id))

def c33470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33470 : Upper (D 7) (R 7) [12,272,33,66,130] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,130] 13 (by decide) (choices 1) [1,64,128] r33470 c33470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17481
  · exact u17482
  · exact u17483

def r33471 : Route 9 := (fun mask => (mask,id))

def c33471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33471 : Upper (D 7) (R 7) [12,272,33,66,160] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,160] 13 (by decide) (choices 1) [1,2,64,128] r33471 c33471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17484
  · exact u17485
  · exact u17486
  · exact u17487

def r33472 : Route 9 := (fun mask => (mask,id))

def c33472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33472 : Upper (D 7) (R 7) [12,272,33,66,192] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,192] 13 (by decide) (choices 1) [1,2,128] r33472 c33472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17488
  · exact u17489
  · exact u17490

def r33473 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33473 : Upper (D 7) (R 7) [12,272,33,192,3] 13 := by
  apply FastRouting.sound _ _ [12,272,33,192,3] 13 (by decide) (choices 1) [2,64] r33473 c33473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17491
  · exact u17492

def b33474 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 16, targets := 194 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6),(4,7)], upper := (rows 13 274 37 200 49 226 194 194 450), lower := (rows 13 274 37 200 49 32 64 128 256), losses := [] }

theorem u33474 : Upper (D 7) (R 7) [12,272,33,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33475 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c33475 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33475 : Upper (D 7) (R 7) [12,272,33,192,34] 13 := by
  apply FastRouting.sound _ _ [12,272,33,192,34] 13 (by decide) (choices 1) [1,2,64] r33475 c33475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17493
  · exact u17494
  · exact u17495

def b33476 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 274 37 200 81 162 226 162 418), lower := (rows 13 274 37 200 81 32 64 128 256), losses := [] }

theorem u33476 : Upper (D 7) (R 7) [12,272,33,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33477 : Route 9 := (fun mask => (mask,id))

def c33477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33477 : Upper (D 7) (R 7) [12,272,33,192,66] 13 := by
  apply FastRouting.sound _ _ [12,272,33,192,66] 13 (by decide) (choices 1) [1,2,128] r33477 c33477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17496
  · exact u17497
  · exact u17498

def r33478 : Route 9 := (fun mask => (mask,id))

def c33478 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33478 : Upper (D 7) (R 7) [12,272,33,192,96] 13 := by
  apply FastRouting.sound _ _ [12,272,33,192,96] 13 (by decide) (choices 1) [1,2,128] r33478 c33478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17499
  · exact u17500
  · exact u17501

def b33479 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 274 37 200 208 35 99 163 291), lower := (rows 13 274 37 200 208 32 64 128 256), losses := [] }

theorem u33479 : Upper (D 7) (R 7) [12,272,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u33479
end Delivery.IrregularNine14.P07
